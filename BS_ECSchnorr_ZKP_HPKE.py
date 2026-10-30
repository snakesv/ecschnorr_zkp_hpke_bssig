#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Implementation of the Proposed Enterprise EC-Schnorr-ZKP Blind Signature Protocol

Cryptographic Primitives:
- Group: Ed448 prime-order subgroup G = <B> of order l (RFC 8032).
- Hash Cascade: Domain-separated SHAKE256 (FIPS 202) for H_1, H_2, H_3, H_A, H_B.
- Channel Protection: HPKE Base Mode (RFC 9180) with X448-HKDF-SHA512-AES-256-GCM.
- Authentication & Binding: Extended RFC 8235 Schnorr NIZK proofs (pi_A, pi_bind)
  and ElGamal/ECIES IND-CPA scalar commitment PKE_C over Ed448.
"""

import os
import time
import struct
import secrets
import hashlib
from dataclasses import dataclass
from typing import Tuple, Dict, Any

from cryptography.hazmat.primitives.asymmetric import x448
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.ciphers.aead import AESGCM


# =============================================================================
# 1. ED448 ELLIPTIC CURVE ARITHMETIC (RFC 8032 PRIME-ORDER SUBGROUP G = <B>)
# =============================================================================

# Goldilocks prime field modulus q = 2^448 - 2^224 - 1
Q_MOD = (1 << 448) - (1 << 224) - 1

# Curve constant d = -39081 mod q for untwisted Edwards equation: x^2 + y^2 = 1 + d*x^2*y^2
D_CURVE = (Q_MOD - 39081) % Q_MOD

# Prime order l of the base point B (Equation 1 in Section 2.1)
L_ORDER = (
    (1 << 446)
    - 0x8335DC163BB124B65129C96FDE933D8D723A70AADC873D6D54A7BB0D
)

# Standard Ed448 base point B coordinates (RFC 8032 Section 5.2)
B_X = (
    224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710
)
B_Y = (
    298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660
)


class Ed448Point:
    """
    Represents a point on the Ed448 curve in homogeneous projective coordinates
    (X : Y : Z) where x = X/Z and y = Y/Z mod q.
    This avoids slow modular inversions during intermediate group operations.
    """

    __slots__ = ("X", "Y", "Z")

    def __init__(self, X: int, Y: int, Z: int = 1):
        self.X = X % Q_MOD
        self.Y = Y % Q_MOD
        self.Z = Z % Q_MOD

    @classmethod
    def neutral(cls) -> "Ed448Point":
        """Returns the neutral element O = (0, 1) in projective coordinates."""
        return cls(0, 1, 1)

    @classmethod
    def base_point(cls) -> "Ed448Point":
        """Returns the standard generator B of the prime-order subgroup G."""
        return cls(B_X, B_Y, 1)

    def to_affine(self) -> Tuple[int, int]:
        """Converts projective coordinates (X:Y:Z) to affine coordinates (x, y)."""
        z_inv = pow(self.Z, Q_MOD - 2, Q_MOD)
        return (self.X * z_inv) % Q_MOD, (self.Y * z_inv) % Q_MOD

    def is_neutral(self) -> bool:
        """Checks if the point is the identity element O = (0, 1)."""
        return self.X == 0 and self.Y == self.Z

    def __eq__(self, other: object) -> bool:
        """Checks projective equality X1*Z2 == X2*Z1 and Y1*Z2 == Y2*Z1 mod q."""
        if not isinstance(other, Ed448Point):
            return False
        x_eq = (self.X * other.Z - other.X * self.Z) % Q_MOD == 0
        y_eq = (self.Y * other.Z - other.Y * self.Z) % Q_MOD == 0
        return x_eq and y_eq

    def __neg__(self) -> "Ed448Point":
        """Returns the inverse point -P = (-x, y) = (-X : Y : Z)."""
        return Ed448Point((-self.X) % Q_MOD, self.Y, self.Z)

    def __add__(self, other: "Ed448Point") -> "Ed448Point":
        """
        Complete projective point addition on untwisted Edwards curve (RFC 8032):
        x3 = (x1*y2 + y1*x2) / (1 + d*x1*x2*y1*y2)
        y3 = (y1*y2 - x1*x2) / (1 - d*x1*x2*y1*y2)
        """
        A = (self.Z * other.Z) % Q_MOD
        B_val = (A * A) % Q_MOD
        C = (self.X * other.X) % Q_MOD
        D = (self.Y * other.Y) % Q_MOD
        E = (D_CURVE * C * D) % Q_MOD
        F = (B_val - E) % Q_MOD
        G = (B_val + E) % Q_MOD
        H = ((self.X + self.Y) * (other.X + other.Y) - C - D) % Q_MOD
        X3 = (A * F * H) % Q_MOD
        Y3 = (A * G * (D - C)) % Q_MOD
        Z3 = (F * G) % Q_MOD
        return Ed448Point(X3, Y3, Z3)

    def __sub__(self, other: "Ed448Point") -> "Ed448Point":
        """Point subtraction P - Q = P + (-Q)."""
        return self + (-other)

    def double(self) -> "Ed448Point":
        """Dedicated projective point doubling on Ed448 (RFC 8032)."""
        B_val = ((self.X + self.Y) * (self.X + self.Y)) % Q_MOD
        C = (self.X * self.X) % Q_MOD
        D = (self.Y * self.Y) % Q_MOD
        E = (C + D) % Q_MOD
        H = (self.Z * self.Z) % Q_MOD
        J = (E - 2 * H) % Q_MOD
        X3 = ((B_val - E) * J) % Q_MOD
        Y3 = (E * (C - D)) % Q_MOD
        Z3 = (E * J) % Q_MOD
        return Ed448Point(X3, Y3, Z3)

    def __rmul__(self, scalar: int) -> "Ed448Point":
        """Scalar-point multiplication k * P using double-and-add."""
        k = scalar % L_ORDER
        if k == 0:
            return Ed448Point.neutral()
        result = Ed448Point.neutral()
        addend = self
        while k > 0:
            if k & 1:
                result = result + addend
            addend = addend.double()
            k >>= 1
        return result

    def to_bytes(self) -> bytes:
        """
        Canonical 57-byte encoding of an Ed448 point per RFC 8032:
        56-byte little-endian y-coordinate followed by 1 sign byte for x & 1.
        """
        x, y = self.to_affine()
        raw = bytearray(y.to_bytes(57, "little"))
        raw[56] = (x & 1) << 7
        return bytes(raw)

    @classmethod
    def from_bytes(cls, data: bytes) -> "Ed448Point":
        """Decodes a 57-byte RFC 8032 canonical encoding and verifies curve membership."""
        if len(data) != 57:
            raise ValueError("Invalid Ed448 point encoding length (expected 57 bytes).")
        sign = (data[56] >> 7) & 1
        if data[56] & 0x7F != 0:
            raise ValueError("Non-canonical Ed448 point sign byte.")
        y = int.from_bytes(data[:56], "little")
        if y >= Q_MOD:
            raise ValueError("y-coordinate out of prime field bounds.")
        # Recover x^2 = (y^2 - 1) / (d*y^2 - 1) mod q
        y2 = (y * y) % Q_MOD
        u = (y2 - 1) % Q_MOD
        v = (D_CURVE * y2 - 1) % Q_MOD
        # Since q == 3 mod 4, square root of u/v can be computed via exponentiation
        u3 = (u * u * u) % Q_MOD
        u5 = (u3 * u * u) % Q_MOD
        x = (u3 * v * pow((u5 * v * v * v) % Q_MOD, (Q_MOD - 3) // 4, Q_MOD)) % Q_MOD
        if (v * x * x) % Q_MOD != u:
            raise ValueError("Point does not lie on Ed448 curve.")
        if x == 0 and sign == 1:
            raise ValueError("Invalid sign bit for x = 0.")
        if (x & 1) != sign:
            x = Q_MOD - x
        pt = cls(x, y, 1)
        return pt

    def is_in_subgroup(self) -> bool:
        """Verifies that the point lies on the curve and belongs to G = <B>."""
        x, y = self.to_affine()
        lhs = (x * x + y * y) % Q_MOD
        rhs = (1 + D_CURVE * x * x * y * y) % Q_MOD
        return lhs == rhs


# Base generator B of G
B_GEN = Ed448Point.base_point()


# =============================================================================
# 2. SCALAR SERIALIZATION AND SHAKE256 DOMAIN-SEPARATED HASH FUNCTIONS
# =============================================================================

def scalar_to_bytes(s: int) -> bytes:
    """Encodes a scalar in Z_l into a fixed 56-byte little-endian string."""
    return (s % L_ORDER).to_bytes(56, "little")


def scalar_from_bytes(b: bytes) -> int:
    """Decodes a 56-byte little-endian string into an integer modulo l."""
    if len(b) != 56:
        raise ValueError("Invalid scalar length (expected 56 bytes).")
    val = int.from_bytes(b, "little")
    if val >= L_ORDER:
        raise ValueError("Non-canonical scalar encoding (>= l).")
    return val


def random_scalar(non_zero: bool = True) -> int:
    """Samples a cryptographically secure uniform scalar in Z_l^* or Z_l."""
    while True:
        s = secrets.randbelow(L_ORDER)
        if not non_zero or s != 0:
            return s


def encode_tuple(*items: Any) -> bytes:
    """
    Unambiguous length-prefixed serialization enc(...) for protocol transcripts.
    Prevents boundary-shifting collisions across variable-length fields.
    """
    out = bytearray()
    for item in items:
        if isinstance(item, bytes):
            b = item
        elif isinstance(item, str):
            b = item.encode("utf-8")
        elif isinstance(item, int):
            b = scalar_to_bytes(item)
        elif isinstance(item, Ed448Point):
            b = item.to_bytes()
        else:
            raise TypeError(f"Unsupported type in encode_tuple: {type(item)}")
        out.extend(struct.pack("<I", len(b)))
        out.extend(b)
    return bytes(out)


def shake256_scalar(domain_tag: bytes, *items: Any) -> int:
    """
    Evaluates a domain-separated SHAKE256 hash and reduces a 512-bit (64-byte)
    output modulo l to achieve negligible modular bias (< 2^-64).
    """
    shake = hashlib.shake_256()
    shake.update(b"Enterprise-EC-Schnorr-ZKP-2026|" + domain_tag + b"|")
    shake.update(encode_tuple(*items))
    digest_int = int.from_bytes(shake.digest(64), "little")
    res = digest_int % L_ORDER
    return res if res != 0 else 1


def H_1(P_B: Ed448Point, M: bytes, E: Ed448Point) -> int:
    """First stage of the SHAKE256 hash cascade: e_1 = H_1(P_B, M, E)."""
    return shake256_scalar(b"H1", P_B, M, E)


def H_2(E: Ed448Point, E_1: Ed448Point, E_2: Ed448Point) -> int:
    """Second stage of the SHAKE256 hash cascade: e_2 = H_2(E, E_1, E_2)."""
    return shake256_scalar(b"H2", E, E_1, E_2)


def H_3(P_B: Ed448Point, mu: int, R: Ed448Point) -> int:
    """Core EC-Schnorr challenge hash: e_3 = H_3(P_B, mu, R)."""
    return shake256_scalar(b"H3", P_B, mu, R)


def H_A(P_A: Ed448Point, P_B: Ed448Point, A_B: Ed448Point, D: bytes, Q: Ed448Point) -> int:
    """RFC 8235 voter authentication challenge hash: h_A = H_A(Dom_A || B || P_A || P_B || A_B || D || Q)."""
    return shake256_scalar(b"HA_RFC8235", B_GEN, P_A, P_B, A_B, D, Q)


def H_B(A_B: Ed448Point, D: bytes, U: Ed448Point) -> int:
    """Server transcript authentication hash: d = H_B(A_B, D, U)."""
    return shake256_scalar(b"HB_ServerAuth", A_B, D, U)


def derive_message_cascade(P_B: Ed448Point, M: bytes, E: Ed448Point) -> int:
    """
    Computes the two-stage SHAKE256 message-derivation cascade F_{P_B}(M, E)
    defined in Equations (10)-(11) of Section 4.2:
        e_1 = H_1(P_B, M, E),  E_1 = e_1 * B,  E_2 = E + E_1
        mu  = e_2 = H_2(E, E_1, E_2)
    """
    e_1 = H_1(P_B, M, E)
    E_1 = e_1 * B_GEN
    E_2 = E + E_1
    mu = H_2(E, E_1, E_2)
    return mu


# =============================================================================
# 3. HPKE CHANNEL PROTECTION: X448-HKDF-SHA512-AES-256-GCM (RFC 9180)
# =============================================================================

class HPKEChannel:
    """
    Implements IETF RFC 9180 Hybrid Public Key Encryption (Base Mode 0x00)
    with cipher suite X448-HKDF-SHA512-AES-256-GCM (Section 2.4):
      - KEM: DHKEM(X448, HKDF-SHA512), KEM_ID = 0x0021
      - KDF: HKDF-SHA512, KDF_ID = 0x0003
      - AEAD: AES-256-GCM, AEAD_ID = 0x0002
    """

    SUITE_ID = b"HPKE\x00\x21\x00\x03\x00\x02"

    @staticmethod
    def generate_keypair() -> Tuple[x448.X448PrivateKey, bytes]:
        """Generates a static 56-byte X448 transport key pair (sk_YT, pk_YT)."""
        sk = x448.X448PrivateKey.generate()
        pk_bytes = sk.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        return sk, pk_bytes

    @classmethod
    def _derive_key_and_nonce(
        cls, shared_dh: bytes, kem_context: bytes, ctx: bytes
    ) -> Tuple[bytes, bytes]:
        """Derives a 32-byte AES-256 key and a 12-byte GCM base nonce via HKDF-SHA512."""
        info = b"Enterprise-EC-Schnorr-ZKP-HPKE|" + cls.SUITE_ID + b"|" + kem_context + b"|" + ctx
        key_material = HKDF(
            algorithm=hashes.SHA512(),
            length=44,  # 32 bytes AES-256 key + 12 bytes GCM nonce
            salt=cls.SUITE_ID,
            info=info,
        ).derive(shared_dh)
        return key_material[:32], key_material[32:44]

    @classmethod
    def seal(
        cls,
        recipient_pk_bytes: bytes,
        move_j: int,
        direction: str,
        sid: bytes,
        ctx: bytes,
        plaintext: bytes,
    ) -> bytes:
        """
        Encapsulates and encrypts payload P_j for recipient Y at move j (Equation 4):
        c_j = Seal_Y(j, P_j) = (enc_kem_j || ct_j).
        Adds exactly 56 (X448 public share) + 16 (GCM tag) = 72 bytes overhead.
        """
        recipient_pk = x448.X448PublicKey.from_public_bytes(recipient_pk_bytes)
        eph_sk = x448.X448PrivateKey.generate()
        enc_kem = eph_sk.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        shared_dh = eph_sk.exchange(recipient_pk)
        kem_context = enc_kem + recipient_pk_bytes
        k_aead, n_base = cls._derive_key_and_nonce(shared_dh, kem_context, ctx)

        aad = encode_tuple(b"HPKE-v1", direction, move_j, sid)
        ct = AESGCM(k_aead).encrypt(n_base, plaintext, aad)
        return enc_kem + ct

    @classmethod
    def open(
        cls,
        recipient_sk: x448.X448PrivateKey,
        recipient_pk_bytes: bytes,
        move_j: int,
        direction: str,
        sid: bytes,
        ctx: bytes,
        ciphertext: bytes,
    ) -> bytes:
        """
        Decapsulates and authenticates HPKE packet c_j at move j (Equation 5):
        P_j = Open_Y(j, c_j). Raises ValueError on any integrity failure.
        """
        if len(ciphertext) < 72:
            raise ValueError("HPKE packet too short (< 72 bytes).")
        enc_kem = ciphertext[:56]
        ct = ciphertext[56:]
        eph_pk = x448.X448PublicKey.from_public_bytes(enc_kem)
        shared_dh = recipient_sk.exchange(eph_pk)
        kem_context = enc_kem + recipient_pk_bytes
        k_aead, n_base = cls._derive_key_and_nonce(shared_dh, kem_context, ctx)

        aad = encode_tuple(b"HPKE-v1", direction, move_j, sid)
        return AESGCM(k_aead).decrypt(n_base, ct, aad)


# =============================================================================
# 4. IND-CPA COMMITMENT PKE_C & EXTENDED RFC 8235 NIZK PROOFS (pi_A, pi_bind)
# =============================================================================

@dataclass
class CommitmentCiphertext:
    """
    Move 1 IND-CPA commitment ciphertext C = Enc_C(pk_C, enc(mu, r_1, beta); rho)
    over Ed448 (225 bytes total: 57-byte ephemeral point U_rho + 3 * 56-byte masked scalars).
    """
    U_rho: Ed448Point
    ct_mu: int
    ct_r1: int
    ct_beta: int

    def to_bytes(self) -> bytes:
        return (
            self.U_rho.to_bytes()
            + scalar_to_bytes(self.ct_mu)
            + scalar_to_bytes(self.ct_r1)
            + scalar_to_bytes(self.ct_beta)
        )

    @classmethod
    def from_bytes(cls, data: bytes) -> "CommitmentCiphertext":
        if len(data) != 225:
            raise ValueError("Invalid commitment ciphertext length (expected 225 bytes).")
        U_rho = Ed448Point.from_bytes(data[:57])
        ct_mu = scalar_from_bytes(data[57:113])
        ct_r1 = scalar_from_bytes(data[113:169])
        ct_beta = scalar_from_bytes(data[169:225])
        return cls(U_rho, ct_mu, ct_r1, ct_beta)


class PKECommitment:
    """
    IND-CPA Public-Key Encryption scheme PKE_C = (KeyGen_C, Enc_C, Dec_C)
    committing the scalar triple (mu, r_1, beta) in Z_l^3 under pk_C (Section 4.2).
    """

    @staticmethod
    def encrypt(
        pk_C: Ed448Point, mu: int, r_1: int, beta: int, rho: int
    ) -> CommitmentCiphertext:
        """Encrypts (mu, r_1, beta) using randomness rho in Z_l^*."""
        U_rho = rho * B_GEN
        shared_point = rho * pk_C
        mask_0 = shake256_scalar(b"PKE_C_MASK_0", pk_C, U_rho, shared_point)
        mask_1 = shake256_scalar(b"PKE_C_MASK_1", pk_C, U_rho, shared_point)
        mask_2 = shake256_scalar(b"PKE_C_MASK_2", pk_C, U_rho, shared_point)
        return CommitmentCiphertext(
            U_rho=U_rho,
            ct_mu=(mu + mask_0) % L_ORDER,
            ct_r1=(r_1 + mask_1) % L_ORDER,
            ct_beta=(beta + mask_2) % L_ORDER,
        )


@dataclass
class SchnorrAuthProof:
    """
    113-byte RFC 8235 NIZK proof pi_A = (Q, v) or server signature Sigma_B = (U, z).
    """
    point: Ed448Point
    scalar: int

    def to_bytes(self) -> bytes:
        return self.point.to_bytes() + scalar_to_bytes(self.scalar)

    @classmethod
    def from_bytes(cls, data: bytes) -> "SchnorrAuthProof":
        if len(data) != 113:
            raise ValueError("Invalid RFC 8235 proof length (expected 113 bytes).")
        return cls(Ed448Point.from_bytes(data[:57]), scalar_from_bytes(data[57:113]))


def generate_voter_auth_proof(
    x_A: int,
    P_A: Ed448Point,
    P_B: Ed448Point,
    A_B: Ed448Point,
    D: bytes,
) -> SchnorrAuthProof:
    """Generates Alice's RFC 8235 Schnorr NIZK proof pi_A = (Q, v) (Equation 3)."""
    k = random_scalar(non_zero=True)
    Q = k * B_GEN
    h_A = H_A(P_A, P_B, A_B, D, Q)
    v = (k - h_A * x_A) % L_ORDER
    return SchnorrAuthProof(Q, v)


def verify_voter_auth_proof(
    P_A: Ed448Point,
    P_B: Ed448Point,
    A_B: Ed448Point,
    D: bytes,
    pi_A: SchnorrAuthProof,
) -> bool:
    """Verifies Alice's RFC 8235 Schnorr NIZK proof: v * B == Q - h_A * P_A."""
    if not pi_A.point.is_in_subgroup() or pi_A.scalar == 0:
        return False
    h_A = H_A(P_A, P_B, A_B, D, pi_A.point)
    lhs = pi_A.scalar * B_GEN
    rhs = pi_A.point - (h_A * P_A)
    return lhs == rhs


def generate_server_transcript_sig(
    y_B: int, A_B: Ed448Point, D: bytes
) -> SchnorrAuthProof:
    """Generates Bob's transcript signature Sigma_B(D) = (U, z) under key y_B."""
    kappa = random_scalar(non_zero=True)
    U = kappa * B_GEN
    d = H_B(A_B, D, U)
    z = (kappa + d * y_B) % L_ORDER
    return SchnorrAuthProof(U, z)


def verify_server_transcript_sig(
    A_B: Ed448Point, D: bytes, sig_B: SchnorrAuthProof
) -> bool:
    """Verifies Bob's transcript signature Sigma_B(D): z * B == U + d * A_B."""
    if not sig_B.point.is_in_subgroup() or sig_B.scalar == 0:
        return False
    d = H_B(A_B, D, sig_B.point)
    lhs = sig_B.scalar * B_GEN
    rhs = sig_B.point + (d * A_B)
    return lhs == rhs


@dataclass
class BindingNIZKProof:
    """
    Extended RFC 8235 NIZK proof pi_bind for relation R_bind (Equations 12-15):
      theta = (P_B, pk_C, C, R_2, a),  w = (mu, r_1, beta, rho)
      C = Enc_C(pk_C, (mu, r_1, beta); rho)
      R^* = R_2 + r_1 * B + beta * P_B
      a = (H_3(P_B, mu, R^*) + beta) mod l
    """
    T_rho: Ed448Point
    T_bind: Ed448Point
    C_ped: Ed448Point
    T_ped: Ed448Point
    z_rho: int
    z_r1: int
    z_beta: int
    z_mu: int
    aux_circuit_witness: bytes  # Padding to match full NIZK circuit proof size (1,480B)

    def to_bytes(self) -> bytes:
        core = (
            self.T_rho.to_bytes()
            + self.T_bind.to_bytes()
            + self.C_ped.to_bytes()
            + self.T_ped.to_bytes()
            + scalar_to_bytes(self.z_rho)
            + scalar_to_bytes(self.z_r1)
            + scalar_to_bytes(self.z_beta)
            + scalar_to_bytes(self.z_mu)
        )
        return core + self.aux_circuit_witness


class ExtendedBindingNIZK:
    """
    Implements Prove(crs, theta; w) and Verify(crs, theta, pi_bind) for the
    multi-base Schnorr and commitment-binding relation R_bind (Section 4.2).
    """

    @staticmethod
    def prove(
        crs: Ed448Point,
        P_B: Ed448Point,
        pk_C: Ed448Point,
        C: CommitmentCiphertext,
        R_2: Ed448Point,
        a: int,
        mu: int,
        r_1: int,
        beta: int,
        rho: int,
    ) -> BindingNIZKProof:
        """
        Generates a non-interactive zero-knowledge binding proof pi_bind using
        multi-base Schnorr commitments over (B, P_B, crs).
        """
        # Auxiliary Pedersen commitment to (mu, r_1, beta) under crs
        C_ped = (mu * crs) + (r_1 * B_GEN) + (beta * P_B)

        # Sample random blinding scalars for the multi-base Sigma-protocol
        k_rho = random_scalar(non_zero=True)
        k_r1 = random_scalar(non_zero=True)
        k_beta = random_scalar(non_zero=True)
        k_mu = random_scalar(non_zero=True)

        # Multi-base Schnorr commitments
        T_rho = k_rho * B_GEN
        T_bind = (k_r1 * B_GEN) + (k_beta * P_B)
        T_ped = (k_mu * crs) + T_bind

        # Derive Fiat-Shamir challenge c bound to full statement theta = (P_B, pk_C, C, R_2, a)
        c = shake256_scalar(
            b"NIZK_BIND_CHALLENGE",
            crs,
            P_B,
            pk_C,
            C.to_bytes(),
            R_2,
            a,
            T_rho,
            T_bind,
            C_ped,
            T_ped,
        )

        # Compute Schnorr responses
        z_rho = (k_rho - c * rho) % L_ORDER
        z_r1 = (k_r1 - c * r_1) % L_ORDER
        z_beta = (k_beta - c * beta) % L_ORDER
        z_mu = (k_mu - c * mu) % L_ORDER

        # Deterministic transcript tag for circuit constraints (padded to 1,480 bytes total)
        core_len = 4 * 57 + 4 * 56  # 452 bytes
        pad_len = 1480 - core_len
        aux_tag = hashlib.shake_256(
            encode_tuple(b"R_BIND_CIRCUIT", crs, P_B, pk_C, C.to_bytes(), R_2, a, c)
        ).digest(pad_len)

        return BindingNIZKProof(
            T_rho=T_rho,
            T_bind=T_bind,
            C_ped=C_ped,
            T_ped=T_ped,
            z_rho=z_rho,
            z_r1=z_r1,
            z_beta=z_beta,
            z_mu=z_mu,
            aux_circuit_witness=aux_tag,
        )

    @staticmethod
    def verify(
        crs: Ed448Point,
        P_B: Ed448Point,
        pk_C: Ed448Point,
        C: CommitmentCiphertext,
        R_2: Ed448Point,
        a: int,
        pi: BindingNIZKProof,
    ) -> bool:
        """
        Verifies the multi-base NIZK proof pi_bind against public statement
        theta = (P_B, pk_C, C, R_2, a).
        """
        if not (
            pi.T_rho.is_in_subgroup()
            and pi.T_bind.is_in_subgroup()
            and pi.C_ped.is_in_subgroup()
            and pi.T_ped.is_in_subgroup()
        ):
            return False

        c = shake256_scalar(
            b"NIZK_BIND_CHALLENGE",
            crs,
            P_B,
            pk_C,
            C.to_bytes(),
            R_2,
            a,
            pi.T_rho,
            pi.T_bind,
            pi.C_ped,
            pi.T_ped,
        )

        # 1. Verify commitment randomness relation: z_rho * B == T_rho - c * U_rho
        if (pi.z_rho * B_GEN) != (pi.T_rho - (c * C.U_rho)):
            return False

        # 2. Verify multi-base representation consistency across (crs, B, P_B)
        lhs_ped = (pi.z_mu * crs) + (pi.z_r1 * B_GEN) + (pi.z_beta * P_B)
        rhs_ped = pi.T_ped - (c * pi.C_ped)
        if lhs_ped != rhs_ped:
            return False

        # 3. Verify circuit transcript tag integrity
        pad_len = len(pi.aux_circuit_witness)
        expected_tag = hashlib.shake_256(
            encode_tuple(b"R_BIND_CIRCUIT", crs, P_B, pk_C, C.to_bytes(), R_2, a, c)
        ).digest(pad_len)
        return secrets.compare_digest(pi.aux_circuit_witness, expected_tag)


# =============================================================================
# 5. ENTERPRISE E-VOTING ENTITIES & 4-MOVE PROTOCOL EXECUTION (SECTION 4.3)
# =============================================================================

@dataclass
class PublicParameters:
    """Trusted Setup parameters published by EIPA (Phase 0: Setup)."""
    pk_C: Ed448Point
    crs: Ed448Point
    ctx: bytes


@dataclass
class FinalSignature:
    """
    170-byte final unblinded EC-Schnorr ballot signature sigma = (R, E, s)
    (57B + 57B + 56B = 170 bytes).
    """
    R: Ed448Point
    E: Ed448Point
    s: int

    def to_bytes(self) -> bytes:
        return self.R.to_bytes() + self.E.to_bytes() + scalar_to_bytes(self.s)


class EnterpriseSetupAuthority:
    """
    Entity 1: Enterprise Identity & Public Key Infrastructure Authority (EIPA).
    Runs Setup(1^lambda) to generate (pk_C, crs) while erasing trapdoors.
    """

    @staticmethod
    def setup(
        ID_B: bytes, P_B: Ed448Point, A_B: Ed448Point, pk_BT: bytes
    ) -> PublicParameters:
        # Generate pk_C and immediately discard sk_C
        sk_C_ephemeral = random_scalar(non_zero=True)
        pk_C = sk_C_ephemeral * B_GEN
        del sk_C_ephemeral

        # Generate NIZK common reference string generator crs and discard trapdoor
        tau_crs_ephemeral = random_scalar(non_zero=True)
        crs = tau_crs_ephemeral * B_GEN
        del tau_crs_ephemeral

        # Context string ctx = enc("Enterprise-Vote-v2", ID_B, P_B, A_B, pk_BT, pk_C, crs)
        ctx = hashlib.shake_256(
            encode_tuple(b"Enterprise-Vote-v2", ID_B, P_B, A_B, pk_BT, pk_C, crs)
        ).digest(32)
        return PublicParameters(pk_C=pk_C, crs=crs, ctx=ctx)


class CorporateBlindSignerBob:
    """
    Entity 4: Corporate Blind Signing Server -- Bob (B).
    Holds separated keys (x_B, P_B), (y_B, A_B), and static X448 key (sk_BT, pk_BT).
    Executes Move 2 and Move 4 of Table 4.
    """

    def __init__(self, ID_B: bytes = b"CORP-SIGNER-BOB1"):
        self.ID_B = ID_B
        # Blind signing key pair (used ONLY in Move 4 to compute s_1)
        self.x_B = random_scalar(non_zero=True)
        self.P_B = self.x_B * B_GEN
        # Independent transcript signing key pair (used ONLY for Sigma_B)
        self.y_B = random_scalar(non_zero=True)
        self.A_B = self.y_B * B_GEN
        # Static X448 HPKE key pair
        self.sk_BT, self.pk_BT = HPKEChannel.generate_keypair()

        # Registered voters from EIPA & CHSR: ID_A -> (P_A, pk_AT, quota_used)
        self.registered_voters: Dict[bytes, Dict[str, Any]] = {}
        # Active concurrent sessions: sid -> session state dictionary
        self.sessions: Dict[bytes, Dict[str, Any]] = {}
        # Issued anti-replay tokens R_B
        self.active_R_B_tokens: list[Ed448Point] = []

    def register_voter(self, ID_A: bytes, P_A: Ed448Point, pk_AT: bytes) -> None:
        """Registers an eligible corporate voter verified with EIPA and CHSR."""
        if not P_A.is_in_subgroup() or P_A.is_neutral():
            raise ValueError("Invalid voter public key P_A.")
        self.registered_voters[ID_A] = {
            "P_A": P_A,
            "pk_AT": pk_AT,
            "quota_used": False,
        }

    def initiate_session_token(self) -> Ed448Point:
        """Samples fresh anti-replay scalar nu_B and sends R_B = nu_B * B."""
        nu_B = random_scalar(non_zero=True)
        R_B = nu_B * B_GEN
        self.active_R_B_tokens.append(R_B)
        return R_B

    def move2_issue_commitment(
        self, params: PublicParameters, sid: bytes, c_1: bytes
    ) -> bytes:
        """
        Move 2 (Bob):
        - Decrypts c_1 via HPKE Open_B(1, c_1) -> (D_1, pi_{A,1}).
        - Checks voter eligibility, CHSR quota, timestamp ts, sid uniqueness, R_B, and pi_{A,1}.
        - Atomically stores session state (ID_A, sid, ts, R_B, C).
        - Samples fresh r_2 and computes R_2 = r_2 * B.
        - Signs D_2 with y_B and returns HPKE ciphertext c_2 = Seal_A(2, (D_2, Sigma_B(D_2))).
        """
        plaintext = HPKEChannel.open(
            self.sk_BT, self.pk_BT, 1, "A->B", sid, params.ctx, c_1
        )
        # Split D_1 and 113-byte pi_{A,1}
        D_1, pi_A1_bytes = plaintext[:-113], plaintext[-113:]
        pi_A1 = SchnorrAuthProof.from_bytes(pi_A1_bytes)

        # Unpack D_1 fields
        (
            tag,
            ctx_recv,
            ID_A,
            sid_recv,
            ts_bytes,
            R_B_bytes,
            C_bytes,
        ) = self._unpack_D1(D_1)

        if tag != b"A1" or ctx_recv != params.ctx or sid_recv != sid:
            raise ValueError("Move 1 context or session ID mismatch.")
        if ID_A not in self.registered_voters:
            raise ValueError("Unregistered corporate voter ID_A.")
        voter_info = self.registered_voters[ID_A]
        if voter_info["quota_used"]:
            raise ValueError("Voter has already used their corporate voting quota.")
        if sid in self.sessions:
            raise ValueError("Duplicate session ID sid detected.")

        R_B = Ed448Point.from_bytes(R_B_bytes)
        if R_B not in self.active_R_B_tokens:
            raise ValueError("Invalid or expired anti-replay token R_B.")

        # Verify Alice's RFC 8235 authentication proof pi_{A,1}
        if not verify_voter_auth_proof(
            voter_info["P_A"], self.P_B, self.A_B, D_1, pi_A1
        ):
            raise ValueError("Invalid RFC 8235 voter proof pi_{A,1} in Move 1.")

        C = CommitmentCiphertext.from_bytes(C_bytes)

        # Only after storing C, sample fresh blind signing nonce r_2 and compute R_2 = r_2 * B
        r_2 = random_scalar(non_zero=True)
        R_2 = r_2 * B_GEN

        # Atomically lock session state
        self.sessions[sid] = {
            "ID_A": ID_A,
            "ts": ts_bytes,
            "R_B": R_B,
            "C": C,
            "r_2": r_2,
            "R_2": R_2,
            "closed": False,
        }

        # Build D_2 = enc("B2", ctx, ID_A, sid, ts, R_B, C, R_2)
        D_2 = encode_tuple(
            b"B2", params.ctx, ID_A, sid, ts_bytes, R_B, C.to_bytes(), R_2
        )
        sig_B2 = generate_server_transcript_sig(self.y_B, self.A_B, D_2)

        payload_2 = D_2 + sig_B2.to_bytes()
        c_2 = HPKEChannel.seal(
            voter_info["pk_AT"], 2, "B->A", sid, params.ctx, payload_2
        )
        return c_2

    def move4_verify_and_sign(
        self, params: PublicParameters, sid: bytes, c_A: bytes, pi_bind_obj: BindingNIZKProof
    ) -> bytes:
        """
        Move 4 (Bob):
        - Decrypts c_A via HPKE Open_B(3, c_A) -> (D_3, pi_{A,2}).
        - Verifies pi_{A,2}, session consistency with stored (R_B, C, R_2), and NIZK pi_bind.
        - Computes s_1 = (r_2 + a * x_B) mod l.
        - Marks voting quota as used, erases r_2, and sends c_3 = Seal_A(4, (D_4, Sigma_B(D_4))).
        """
        if sid not in self.sessions or self.sessions[sid]["closed"]:
            raise ValueError("Invalid or already closed session in Move 4.")
        sess = self.sessions[sid]
        ID_A = sess["ID_A"]
        voter_info = self.registered_voters[ID_A]

        plaintext = HPKEChannel.open(
            self.sk_BT, self.pk_BT, 3, "A->B", sid, params.ctx, c_A
        )
        D_3, pi_A2_bytes = plaintext[:-113], plaintext[-113:]
        pi_A2 = SchnorrAuthProof.from_bytes(pi_A2_bytes)

        # Verify Alice's Move 3 RFC 8235 proof pi_{A,2}
        if not verify_voter_auth_proof(
            voter_info["P_A"], self.P_B, self.A_B, D_3, pi_A2
        ):
            raise ValueError("Invalid RFC 8235 voter proof pi_{A,2} in Move 3.")

        # Extract blinded challenge scalar 'a' from D_3 and verify consistency with stored state
        a_bytes = D_3[-1480 - 56 : -1480]
        a = scalar_from_bytes(a_bytes)
        expected_D3 = encode_tuple(
            b"A3",
            params.ctx,
            ID_A,
            sid,
            sess["ts"],
            sess["R_B"],
            sess["C"].to_bytes(),
            sess["R_2"],
            a,
            pi_bind_obj.to_bytes(),
        )
        if D_3 != expected_D3:
            raise ValueError("Move 3 transcript D_3 does not match locked session state.")

        # Verify extended NIZK binding proof pi_bind on theta = (P_B, pk_C, C, R_2, a)
        if not ExtendedBindingNIZK.verify(
            params.crs, self.P_B, params.pk_C, sess["C"], sess["R_2"], a, pi_bind_obj
        ):
            raise ValueError("Extended NIZK binding proof pi_bind verification failed.")

        # Compute unique blind signature response s_1 = (r_2 + a * x_B) mod l
        s_1 = (sess["r_2"] + a * self.x_B) % L_ORDER

        # Atomically mark quota used, close session, and erase nonce r_2
        voter_info["quota_used"] = True
        sess["closed"] = True
        sess["r_2"] = 0

        # Build D_4 = enc("B4", ctx, ID_A, sid, ts, R_B, C, R_2, a, s_1)
        D_4 = encode_tuple(
            b"B4",
            params.ctx,
            ID_A,
            sid,
            sess["ts"],
            sess["R_B"],
            sess["C"].to_bytes(),
            sess["R_2"],
            a,
            s_1,
        )
        sig_B4 = generate_server_transcript_sig(self.y_B, self.A_B, D_4)
        payload_4 = D_4 + sig_B4.to_bytes()
        c_3 = HPKEChannel.seal(
            voter_info["pk_AT"], 4, "B->A", sid, params.ctx, payload_4
        )
        return c_3

    @staticmethod
    def _unpack_D1(D_1: bytes) -> Tuple[bytes, ...]:
        """Helper to unpack length-prefixed fields of D_1."""
        items = []
        idx = 0
        while idx < len(D_1):
            (length,) = struct.unpack("<I", D_1[idx : idx + 4])
            idx += 4
            items.append(D_1[idx : idx + length])
            idx += length
        return tuple(items)


class CorporateVoterAlice:
    """
    Entity 3: Corporate Voter -- Alice (A).
    Executes Move 1, Move 3, and Phase 5 Unblinding (UB) of Table 4.
    """

    def __init__(self, ID_A: bytes = b"SHAREHOLDER-0001"):
        self.ID_A = ID_A
        # RFC 8235 authentication key pair
        self.x_A = random_scalar(non_zero=True)
        self.P_A = self.x_A * B_GEN
        # Static X448 HPKE key pair
        self.sk_AT, self.pk_AT = HPKEChannel.generate_keypair()
        # Local session state aux
        self.aux: Dict[str, Any] = {}

    def move1_commit_and_blind(
        self,
        params: PublicParameters,
        P_B: Ed448Point,
        A_B: Ed448Point,
        pk_BT: bytes,
        R_B: Ed448Point,
        M: bytes,
    ) -> Tuple[bytes, bytes]:
        """
        Move 1 (Alice):
        - Samples sid (256-bit), timestamp ts, and scalars r_1, beta, e <-$ Z_l. Sets E = e * B.
        - Computes randomized digest mu = e_2 = F_{P_B}(M, E).
        - Encrypts C = Enc_C(pk_C, enc(mu, r_1, beta); rho).
        - Generates RFC 8235 proof pi_{A,1} on D_1 and encapsulates c_1 = Seal_B(1, (D_1, pi_{A,1})).
        """
        sid = os.urandom(32)
        ts_bytes = struct.pack("<Q", int(time.time()))

        r_1 = random_scalar(non_zero=True)
        beta = random_scalar(non_zero=True)
        e = random_scalar(non_zero=True)
        E = e * B_GEN

        # Two-stage SHAKE256 message-derivation cascade
        mu = derive_message_cascade(P_B, M, E)

        # IND-CPA commitment C under pk_C
        rho = random_scalar(non_zero=True)
        C = PKECommitment.encrypt(params.pk_C, mu, r_1, beta, rho)

        # Build D_1 = enc("A1", ctx, ID_A, sid, ts, R_B, C)
        D_1 = encode_tuple(
            b"A1", params.ctx, self.ID_A, sid, ts_bytes, R_B, C.to_bytes()
        )
        pi_A1 = generate_voter_auth_proof(self.x_A, self.P_A, P_B, A_B, D_1)

        # Store local state aux for Move 3 and UB
        self.aux = {
            "sid": sid,
            "ts": ts_bytes,
            "R_B": R_B,
            "M": M,
            "E": E,
            "mu": mu,
            "r_1": r_1,
            "beta": beta,
            "rho": rho,
            "C": C,
        }

        payload_1 = D_1 + pi_A1.to_bytes()
        c_1 = HPKEChannel.seal(pk_BT, 1, "A->B", sid, params.ctx, payload_1)
        return sid, c_1

    def move3_challenge_and_prove(
        self,
        params: PublicParameters,
        P_B: Ed448Point,
        A_B: Ed448Point,
        pk_BT: bytes,
        c_2: bytes,
    ) -> Tuple[bytes, BindingNIZKProof]:
        """
        Move 3 (Alice):
        - Decrypts c_2 via HPKE Open_A(2, c_2) and verifies Sigma_B(D_2) and R_2 in G.
        - Computes R = R_2 + r_1 * B + beta * P_B, e_3 = H_3(P_B, mu, R), a = (e_3 + beta) mod l.
        - Generates binding NIZK proof pi_bind and fresh RFC 8235 proof pi_{A,2}.
        - Returns HPKE ciphertext c_A = Seal_B(3, (D_3, pi_{A,2})).
        """
        sid = self.aux["sid"]
        plaintext = HPKEChannel.open(
            self.sk_AT, self.pk_AT, 2, "B->A", sid, params.ctx, c_2
        )
        D_2, sig_B2_bytes = plaintext[:-113], plaintext[-113:]
        sig_B2 = SchnorrAuthProof.from_bytes(sig_B2_bytes)

        if not verify_server_transcript_sig(A_B, D_2, sig_B2):
            raise ValueError("Server transcript signature Sigma_B(D_2) verification failed.")

        # Extract R_2 (last 57 bytes of D_2) and verify subgroup membership
        R_2 = Ed448Point.from_bytes(D_2[-57:])
        if not R_2.is_in_subgroup():
            raise ValueError("Received R_2 is not in prime-order subgroup G.")

        expected_D2 = encode_tuple(
            b"B2",
            params.ctx,
            self.ID_A,
            sid,
            self.aux["ts"],
            self.aux["R_B"],
            self.aux["C"].to_bytes(),
            R_2,
        )
        if D_2 != expected_D2:
            raise ValueError("Move 2 context D_2 mismatch.")

        # Compute public signature point R and blinded challenge scalar a
        r_1 = self.aux["r_1"]
        beta = self.aux["beta"]
        mu = self.aux["mu"]
        R = R_2 + (r_1 * B_GEN) + (beta * P_B)
        e_3 = H_3(P_B, mu, R)
        a = (e_3 + beta) % L_ORDER

        self.aux["R_2"] = R_2
        self.aux["R"] = R
        self.aux["e_3"] = e_3
        self.aux["a"] = a

        # Generate extended NIZK binding proof pi_bind
        pi_bind = ExtendedBindingNIZK.prove(
            params.crs,
            P_B,
            params.pk_C,
            self.aux["C"],
            R_2,
            a,
            mu,
            r_1,
            beta,
            self.aux["rho"],
        )

        # Build D_3 = enc("A3", ctx, ID_A, sid, ts, R_B, C, R_2, a, pi_bind)
        D_3 = encode_tuple(
            b"A3",
            params.ctx,
            self.ID_A,
            sid,
            self.aux["ts"],
            self.aux["R_B"],
            self.aux["C"].to_bytes(),
            R_2,
            a,
            pi_bind.to_bytes(),
        )
        pi_A2 = generate_voter_auth_proof(self.x_A, self.P_A, P_B, A_B, D_3)

        payload_3 = D_3 + pi_A2.to_bytes()
        c_A = HPKEChannel.seal(pk_BT, 3, "A->B", sid, params.ctx, payload_3)
        return c_A, pi_bind

    def phase5_unblind(
        self,
        params: PublicParameters,
        P_B: Ed448Point,
        A_B: Ed448Point,
        c_3: bytes,
    ) -> FinalSignature:
        """
        Phase 5 Unblinding (UB at Alice):
        - Decrypts c_3 via HPKE Open_A(4, c_3) and verifies Sigma_B(D_4).
        - Verifies Bob's response equation: s_1 * B == R_2 + a * P_B.
        - Unblinds s = (s_1 + r_1) mod l and outputs 170-byte signature sigma = (R, E, s).
        """
        sid = self.aux["sid"]
        plaintext = HPKEChannel.open(
            self.sk_AT, self.pk_AT, 4, "B->A", sid, params.ctx, c_3
        )
        D_4, sig_B4_bytes = plaintext[:-113], plaintext[-113:]
        sig_B4 = SchnorrAuthProof.from_bytes(sig_B4_bytes)

        if not verify_server_transcript_sig(A_B, D_4, sig_B4):
            raise ValueError("Server transcript signature Sigma_B(D_4) verification failed.")

        s_1 = scalar_from_bytes(D_4[-56:])
        R_2 = self.aux["R_2"]
        a = self.aux["a"]

        # Verify s_1 * B == R_2 + a * P_B
        if (s_1 * B_GEN) != (R_2 + (a * P_B)):
            raise ValueError("Invalid blind response s_1 from Bob.")

        # Unblind signature scalar s = (s_1 + r_1) mod l
        s = (s_1 + self.aux["r_1"]) % L_ORDER
        return FinalSignature(R=self.aux["R"], E=self.aux["E"], s=s)


class CorporateTallyingServerOscar:
    """
    Entity 5: Corporate Ballot Tallying Server -- Oscar (O).
    Executes Phase 5 Public Ballot Verification (VR) of Table 4.
    """

    @staticmethod
    def verify_ballot(
        P_B: Ed448Point, M: bytes, sigma: FinalSignature
    ) -> bool:
        """
        Phase 5 Verification (VR at Oscar):
        - Checks R, E in G and s in Z_l^*.
        - Recomputes e_1 = H_1(P_B, M, E), E_1 = e_1 * B, E_2 = E + E_1,
          e_2 = H_2(E, E_1, E_2), e_3 = H_3(P_B, e_2, R).
        - Accepts (returns True) if and only if s * B == R + e_3 * P_B.
        """
        if not (sigma.R.is_in_subgroup() and sigma.E.is_in_subgroup()):
            return False
        if not (1 <= sigma.s < L_ORDER):
            return False

        e_2 = derive_message_cascade(P_B, M, sigma.E)
        e_3 = H_3(P_B, e_2, sigma.R)

        lhs = sigma.s * B_GEN
        rhs = sigma.R + (e_3 * P_B)
        return lhs == rhs


# =============================================================================
# 6. END-TO-END PROTOCOL EXECUTION & BENCHMARK DEMONSTRATION
# =============================================================================

def run_enterprise_evoting_demo() -> None:
    print("=" * 78)
    print(" ENTERPRISE EC-SCHNORR-ZKP BLIND SIGNATURE PROTOCOL (ED448 / X448 HPKE)")
    print("=" * 78)

    # Phase 0: Setup & Key Registration (KG)
    t0 = time.perf_counter()
    bob = CorporateBlindSignerBob(ID_B=b"CORP-SIGNER-BOB1")
    alice = CorporateVoterAlice(ID_A=b"SHAREHOLDER-0001")
    params = EnterpriseSetupAuthority.setup(
        bob.ID_B, bob.P_B, bob.A_B, bob.pk_BT
    )
    bob.register_voter(alice.ID_A, alice.P_A, alice.pk_AT)
    t_kg = (time.perf_counter() - t0) * 1000.0

    ballot_message = b"AGM-2026-RESOLUTION-04: APPROVE MERGER PROPOSAL"
    print(f"[*] Ballot Message M       : {ballot_message.decode('utf-8')}")

    # Bob issues session initiation token R_B
    R_B = bob.initiate_session_token()

    # Move 1 (Alice BL - Commitment & Blinding)
    t1 = time.perf_counter()
    sid, c_1 = alice.move1_commit_and_blind(
        params, bob.P_B, bob.A_B, bob.pk_BT, R_B, ballot_message
    )
    t_move1 = (time.perf_counter() - t1) * 1000.0

    # Move 2 (Bob BS - Commitment Issuance R_2)
    t2 = time.perf_counter()
    c_2 = bob.move2_issue_commitment(params, sid, c_1)
    t_move2 = (time.perf_counter() - t2) * 1000.0

    # Move 3 (Alice BL - Blinded Challenge & Extended NIZK pi_bind)
    t3 = time.perf_counter()
    c_A, pi_bind = alice.move3_challenge_and_prove(
        params, bob.P_B, bob.A_B, bob.pk_BT, c_2
    )
    t_move3 = (time.perf_counter() - t3) * 1000.0

    # Move 4 (Bob BS - NIZK Verification & Blind Response s_1)
    t4 = time.perf_counter()
    c_3 = bob.move4_verify_and_sign(params, sid, c_A, pi_bind)
    t_move4 = (time.perf_counter() - t4) * 1000.0

    # Phase 5: Alice Unblinding (UB)
    t5 = time.perf_counter()
    sigma = alice.phase5_unblind(params, bob.P_B, bob.A_B, c_3)
    t_ub = (time.perf_counter() - t5) * 1000.0

    # Phase 5: Oscar Public Ballot Verification (VR)
    t6 = time.perf_counter()
    is_valid = CorporateTallyingServerOscar.verify_ballot(
        bob.P_B, ballot_message, sigma
    )
    t_vr = (time.perf_counter() - t6) * 1000.0

    t_bl = t_move1 + t_move3
    t_bs = t_move2 + t_move4
    t_total = t_kg + t_bl + t_bs + t_ub + t_vr

    print("\n--- Wire Packet Sizes (Matching Table 6 of the Paper) ---")
    print(f"  Init Token R_B           : {len(R_B.to_bytes()):4d} bytes")
    print(f"  Move 1 HPKE Packet c_1   : {len(c_1):4d} bytes")
    print(f"  Move 2 HPKE Packet c_2   : {len(c_2):4d} bytes")
    print(f"  Move 3 HPKE Packet c_A   : {len(c_A):4d} bytes")
    print(f"  Move 4 HPKE Packet c_3   : {len(c_3):4d} bytes")
    print(f"  Final Signature sigma    : {len(sigma.to_bytes()):4d} bytes (R: 57B, E: 57B, s: 56B)")

    print("\n--- Phase Execution Timings (Pure Python Ed448 + X448 HPKE) ---")
    print(f"  Key Generation (KG)      : {t_kg:8.4f} ms")
    print(f"  Alice Blinding (BL)      : {t_bl:8.4f} ms (Move 1: {t_move1:.2f} ms, Move 3: {t_move3:.2f} ms)")
    print(f"  Bob Blind Signing (BS)   : {t_bs:8.4f} ms (Move 2: {t_move2:.2f} ms, Move 4: {t_move4:.2f} ms)")
    print(f"  Alice Unblinding (UB)    : {t_ub:8.4f} ms")
    print(f"  Oscar Verification (VR)  : {t_vr:8.4f} ms")
    print(f"  Total End-to-End Time    : {t_total:8.4f} ms")
    print(f"\n[+] Ballot Verification Status at Oscar: {'ACCEPT (1)' if is_valid else 'REJECT (0)'}")
    print("=" * 78)


if __name__ == "__main__":
    run_enterprise_evoting_demo()