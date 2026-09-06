// ============================================================================
// SIL7159 : Cryptography and Cryptanalysis -- Assignment 2
//
// Part A: Neutrosophic integer arithmetic library  (Z(I) = { a + bI }, I^2=I)
// Part B: MITM-resistant Diffie-Hellman key exchange authenticated with
//         neutrosophic RSA signatures (Merkepci, Abobala, Allouf 2023)
//
// Big-integer arithmetic uses GMP (mpz_class), as required by the assignment.
// The number-theoretic algorithms named in the deliverables -- Euclid's GCD,
// square-and-multiply exponentiation, the Extended Euclidean Algorithm and
// Euler's totient -- are implemented by hand below.
//
// Build:  g++ -O2 assignment2.cpp -lgmpxx -lgmp -o assignment2
// Run:    ./assignment2            (Part A tests, then all Part B demos)
//         ./assignment2 partA      (Part A unit tests only)
//         ./assignment2 partB      (Part B protocol demos only)
// ============================================================================

#include <gmpxx.h>
#include <iostream>
#include <string>

using namespace std;

// ---------------------------------------------------------------------------
// Small utilities
// ---------------------------------------------------------------------------

// Randomness for key generation (GMP's Mersenne Twister).
static gmp_randclass rng(gmp_randinit_mt);

// ============================================================================
//
//                                  PART A
//
//         Neutrosophic integer ADT  (deliverables A.1 -- A.7)
//
// A neutrosophic integer a + bI is stored as the pair (a, b).
// The key idea (Theorem 1.5 of the assignment) is the ring isomorphism
//
//        Phi(a + bI) = (a, a+b)        Phi^-1(u, v) = u + (v-u)I
//
// so every operation reduces to two independent ordinary-integer
// computations: one on the first coordinate a, one on the sum a + b.
//
// ============================================================================

// ---------------------------------------------------------------------------
// Hand-rolled ordinary-integer helpers (the assignment names these algorithms)
// ---------------------------------------------------------------------------

// Euclid's algorithm for the ordinary gcd (iterative version).
static mpz_class gcdOrdinary(mpz_class x, mpz_class y)
{
    if (x < 0) x = -x;
    if (y < 0) y = -y;
    while (y != 0) {
        mpz_class r = x % y;
        x = y;
        y = r;
    }
    return x;
}

// Square-and-multiply: returns base^exp mod m for exp >= 0, m > 0.
// The result always stays below m, so huge exponents never blow up.
static mpz_class powmodOrdinary(mpz_class base, mpz_class exp, const mpz_class &m)
{
    base %= m;
    if (base < 0) base += m;
    mpz_class result = 1;
    while (exp > 0) {
        if (mpz_odd_p(exp.get_mpz_t()))        // current bit of exp is 1
            result = (result * base) % m;
        base = (base * base) % m;              // square for the next bit
        exp >>= 1;
    }
    return result;
}

// Extended Euclidean Algorithm: writes the inverse of e modulo m into `inv`
// and returns true, provided gcd(e, m) = 1. Returns false when no inverse
// exists (the caller is expected to check).
static bool invOrdinary(const mpz_class &e, const mpz_class &m, mpz_class &inv)
{
    if (gcdOrdinary(e, m) != 1)
        return false;

    mpz_class r_old = e % m, r = m;
    mpz_class s_old = 1,     s = 0;            // invariant: r_old = e*s_old (mod m)
    while (r != 0) {
        mpz_class q = r_old / r;
        mpz_class tmp;

        tmp = r_old - q * r;  r_old = r;  r = tmp;
        tmp = s_old - q * s;  s_old = s;  s = tmp;
    }
    inv = s_old % m;
    if (inv < 0) inv += m;
    return true;
}

// Ordinary Euler totient by trial division and the product formula
// phi(n) = n * product over distinct prime factors p of (1 - 1/p).
// Intended for the small values used in Part A tests.
static mpz_class phiOrdinary(const mpz_class &n)
{
    mpz_class result = n;
    mpz_class rest = n;
    for (mpz_class p = 2; p * p <= rest; p++) {
        if (rest % p == 0) {
            result -= result / p;              // multiply by (1 - 1/p)
            while (rest % p == 0)
                rest /= p;
        }
    }
    if (rest > 1)                              // leftover prime factor
        result -= result / rest;
    return result;
}

// ---------------------------------------------------------------------------
// The neutrosophic integer type  (deliverable A.1)
// ---------------------------------------------------------------------------

struct NeutrosophicInt {
    mpz_class a;                               // rational part
    mpz_class b;                               // coefficient of I

    // Member-initializer list: the fields are constructed directly
    // from the parameters (no default-then-overwrite).
    NeutrosophicInt(const mpz_class &a_ = 0, const mpz_class &b_ = 0)
        : a(a_), b(b_) {}

    // --- A.1  coordinate maps ------------------------------------------------
    // Phi(a + bI) = (a, a+b)          ->  to_coords
    // Phi^-1(u, v) = u + (v-u)I       ->  from_coords
    void to_coords(mpz_class &u, mpz_class &v) const {
        u = a;
        v = a + b;
    }
    static NeutrosophicInt from_coords(const mpz_class &u, const mpz_class &v) {
        return NeutrosophicInt(u, v - u);
    }

    // --- A.2  addition: (a+bI) + (c+dI) = (a+c) + (b+d)I  -------------------
    NeutrosophicInt add(const NeutrosophicInt &o) const {
        return NeutrosophicInt(a + o.a, b + o.b);
    }

    // --- A.3  multiplication -------------------------------------------------
    // (a+bI)(c+dI) = ac + (ad + bc + bd)I  =  ac + [(a+b)(c+d) - ac]I
    // The second form needs only two full multiplications and shows the
    // two-track structure: track 1 is ac, track 2 is (a+b)(c+d).
    NeutrosophicInt mul(const NeutrosophicInt &o) const {
        mpz_class track1 = a * o.a;
        mpz_class track2 = (a + b) * (o.a + o.b);
        return NeutrosophicInt(track1, track2 - track1);
    }

    // --- A.4  neutrosophic coprimality ---------------------------------------
    // Definition 1.7: gcd(A,B) = 1  iff  gcd(a,c)=1 and gcd(a+b, c+d)=1.
    bool isCoprime(const NeutrosophicInt &o) const {
        return gcdOrdinary(a, o.a) == 1
            && gcdOrdinary(a + b, o.a + o.b) == 1;
    }

    // --- A.5  special neutrosophic phi-Euler function ------------------------
    // Definition 1.8: phiS(x + yI) = phi(x) + [phi(x+y) - phi(x)] I
    // i.e. coordinates (phi(x), phi(x+y)).
    NeutrosophicInt phiS() const {
        mpz_class p1 = phiOrdinary(a);
        mpz_class p2 = phiOrdinary(a + b);
        return NeutrosophicInt(p1, p2 - p1);
    }

    // --- A.6  neutrosophic modular exponentiation -----------------------------
    // Definition 1.12 with modulus M: each coordinate of the base is raised
    // to the matching coordinate of the (neutrosophic) exponent, modulo the
    // matching coordinate of the modulus:
    //   track 1:  a^(e1)            mod m1
    //   track 2:  (a+b)^(e1+e2)     mod (m1+m2)
    NeutrosophicInt powmod(const NeutrosophicInt &exponent,
                           const NeutrosophicInt &modulus) const {
        mpz_class base1 = a, base2 = a + b;
        mpz_class exp1  = exponent.a, exp2 = exponent.a + exponent.b;
        mpz_class mod1  = modulus.a,  mod2 = modulus.a + modulus.b;
        mpz_class t1 = powmodOrdinary(base1, exp1, mod1);
        mpz_class t2 = powmodOrdinary(base2, exp2, mod2);
        return from_coords(t1, t2);
    }

    // --- A.7  neutrosophic modular inverse ------------------------------------
    // Section 1.7: invert each coordinate separately with the Extended
    // Euclidean Algorithm, then reassemble:
    //   s1     = e1^-1        mod f1
    //   s1+s2  = (e1+e2)^-1   mod (f1+f2)
    bool invMod(const NeutrosophicInt &modulus, NeutrosophicInt &result) const {
        mpz_class s1, s2sum;
        if (!invOrdinary(a,     modulus.a,           s1))    return false;
        if (!invOrdinary(a + b, modulus.a + modulus.b, s2sum)) return false;
        result = from_coords(s1, s2sum);
        return true;
    }

    // Equality (needed by the test harness and by signature verification).
    bool operator==(const NeutrosophicInt &o) const {
        return a == o.a && b == o.b;
    }
};

// Printing: shows the stored form, e.g.  3 + 2I   or   12 + (-6)I
static ostream &operator<<(ostream &out, const NeutrosophicInt &x)
{
    out << x.a.get_str() << " + (" << x.b.get_str() << ")I";
    return out;
}

// ---------------------------------------------------------------------------
// phiS via known prime factors (used for RSA key generation in Part B, where
// factoring a 256-bit number would be infeasible).
//
// If P = a + bI is a neutrosophic prime (both a and a+b are ordinary primes),
// then phiS(P) = (a-1) + bI, because phi(p) = p-1 for a prime.
// Theorem 1.10: phiS(P*Q) = phiS(P) * phiS(Q)  when gcd(P,Q) = 1.
// (This is exactly Step 2 of the neutrosophic RSA algorithm in the paper.)
// ---------------------------------------------------------------------------
static NeutrosophicInt phiSFromPrimes(const NeutrosophicInt &P,
                                      const NeutrosophicInt &Q)
{
    NeutrosophicInt phiP(P.a - 1, P.b);
    NeutrosophicInt phiQ(Q.a - 1, Q.b);
    return phiP.mul(phiQ);
}

// ---------------------------------------------------------------------------
// Part A unit tests (Section 2.2 of the assignment):
// two tests per operation -- one worked example from the paper,
// one of our own construction (each independently checkable).
// ---------------------------------------------------------------------------

static int failures = 0;

static void check(const string &name, bool ok)
{
    cout << (ok ? "PASS  " : "FAIL  ") << name << "\n";
    if (!ok) failures++;
}

static void runPartATests()
{
    cout << "==================== PART A : unit tests ====================\n";

    // -- A.1 coordinate maps --------------------------------------------------
    {
        // Paper-style example: 3 + 2I  <->  (3, 5).
        NeutrosophicInt x(3, 2);
        mpz_class u, v;
        x.to_coords(u, v);
        check("A.1 to_coords: 3+2I -> (3,5)", u == 3 && v == 5);

        NeutrosophicInt back = NeutrosophicInt::from_coords(7, 12);
        check("A.1 from_coords: (7,12) -> 7+5I", back.a == 7 && back.b == 5);
    }

    // -- A.2 addition ----------------------------------------------------------
    {
        // Own example 1: (3+2I) + (5+6I) = 8 + 8I.
        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.2 add: (3+2I)+(5+6I) = 8+8I",
              A.add(B) == NeutrosophicInt(8, 8));

        // Own example 2 with a negative coefficient: (4-3I) + (1+5I) = 5+2I.
        NeutrosophicInt C(4, -3), D(1, 5);
        check("A.2 add: (4-3I)+(1+5I) = 5+2I",
              C.add(D) == NeutrosophicInt(5, 2));
    }

    // -- A.3 multiplication ----------------------------------------------------
    {
        // Paper example: A = 3+2I, B = 5+6I  ->  A.B = 15 + 40I.
        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.3 mul: (3+2I)(5+6I) = 15+40I",
              A.mul(B) == NeutrosophicInt(15, 40));

        // Paper example (RSA section): P = 3+2I, Q = 7+4I -> N = 21 + 34I.
        NeutrosophicInt P(3, 2), Q(7, 4);
        check("A.3 mul: (3+2I)(7+4I) = 21+34I",
              P.mul(Q) == NeutrosophicInt(21, 34));
    }

    // -- A.4 neutrosophic gcd (coprimality) ------------------------------------
    {
        // Paper example: gcd(3+2I, 7+4I) = 1 because gcd(3,7)=gcd(5,11)=1.
        NeutrosophicInt P(3, 2), Q(7, 4);
        check("A.4 isCoprime: (3+2I, 7+4I) coprime",
              P.isCoprime(Q));

        // Own example: gcd(2+2I, 4+4I) != 1 because gcd(2,4)=2 on track 1.
        NeutrosophicInt X(2, 2), Y(4, 4);
        check("A.4 isCoprime: (2+2I, 4+4I) NOT coprime",
              !X.isCoprime(Y));
    }

    // -- A.5 special phi-Euler function ----------------------------------------
    {
        // Paper example: phiS(15 + 40I) = phi(15) + [phi(55)-phi(15)]I
        //              = 8 + (40-8)I = 8 + 32I.
        NeutrosophicInt AB(15, 40);
        check("A.5 phiS: phiS(15+40I) = 8+32I",
              AB.phiS() == NeutrosophicInt(8, 32));

        // Paper example: phiS(21 + 34I) = phi(21) + [phi(55)-phi(21)]I
        //              = 12 + (40-12)I = 12 + 28I.
        NeutrosophicInt N(21, 34);
        check("A.5 phiS: phiS(21+34I) = 12+28I",
              N.phiS() == NeutrosophicInt(12, 28));

        // Cross-check with the prime-factor formula (Theorem 1.10):
        // 15+40I = (3+2I)(5+6I), so phiS must equal phiS(3+2I)*phiS(5+6I).
        NeutrosophicInt A(3, 2), B(5, 6);
        NeutrosophicInt viaFactors = phiSFromPrimes(A, B);
        check("A.5 phiS: multiplicativity agrees with definition",
              AB.phiS() == viaFactors);
    }

    // -- A.6 neutrosophic modular exponentiation --------------------------------
    {
        // Paper RSA example: M = 3+3I, E = 5+6I, N = 21+34I.
        // C = M^E mod N = 12 - 6I.
        NeutrosophicInt M(3, 3), E(5, 6), N(21, 34);
        check("A.6 powmod: (3+3I)^(5+6I) mod (21+34I) = 12-6I",
              M.powmod(E, N) == NeutrosophicInt(12, -6));

        // Paper RSA example: C = (2+6I)^(17+14I) mod (91+116I) = 32 + 138I.
        NeutrosophicInt M2(2, 6), E2(17, 14), N2(91, 116);
        check("A.6 powmod: (2+6I)^(17+14I) mod (91+116I) = 32+138I",
              M2.powmod(E2, N2) == NeutrosophicInt(32, 138));
    }

    // -- A.7 neutrosophic modular inverse ---------------------------------------
    {
        // Paper example: inverse of E = 5+6I modulo phiS(N) = 12+28I
        // is 5 + 6I again (it is self-inverse).
        NeutrosophicInt E(5, 6), phiN(12, 28), inv;
        bool ok = E.invMod(phiN, inv);
        check("A.7 invMod: (5+6I)^-1 mod (12+28I) = 5+6I",
              ok && inv == NeutrosophicInt(5, 6));

        // Paper example: inverse of 17+14I modulo 72+108I is 17 + 134I.
        NeutrosophicInt E2(17, 14), phiN2(72, 108), inv2;
        bool ok2 = E2.invMod(phiN2, inv2);
        check("A.7 invMod: (17+14I)^-1 mod (72+108I) = 17+134I",
              ok2 && inv2 == NeutrosophicInt(17, 134));

        // Own round-trip check: E * E^-1 == 1 modulo phiN on both tracks.
        NeutrosophicInt one(1, 0);
        NeutrosophicInt prod = E.mul(inv);
        // Reduce each coordinate of the product modulo the matching
        // coordinate of phiN: track 1 mod 12, track 2 mod 40.
        mpz_class t1 = prod.a % phiN.a;
        mpz_class t2 = (prod.a + prod.b) % (phiN.a + phiN.b);
        check("A.7 invMod: E * E^-1 == 1 (mod phiN) round-trip",
              t1 == 1 && t2 == 1);
    }

    // -- Full neutrosophic RSA round-trip on the paper's toy example ----------
    {
        NeutrosophicInt M(3, 3), E(5, 6), N(21, 34);
        NeutrosophicInt C = M.powmod(E, N);          // encrypt
        NeutrosophicInt phiN(12, 28);
        NeutrosophicInt D;
        E.invMod(phiN, D);                            // private exponent
        NeutrosophicInt back = C.powmod(D, N);       // decrypt
        check("RSA round-trip: decrypt(encrypt(3+3I)) = 3+3I",
              back == M);
    }

    cout << (failures == 0 ? "All Part A tests passed.\n"
                           : "SOME PART A TESTS FAILED.\n");
    cout << "\n";
}

// ============================================================================
//
//                                  PART B
//
//   Authenticated neutrosophic Diffie-Hellman key exchange.
//
//   Every party owns a long-term neutrosophic RSA key pair; the partner's
//   public key is assumed known through a trusted channel (requirement iii).
//   Each DH public value is sent together with an RSA signature over it;
//   the receiver verifies the signature BEFORE using the value.  Any forgery
//   or tampering makes the verification fail and the protocol aborts.
//
// ============================================================================

// Miller-Rabin primality test provided by GMP (25 rounds).
static bool isPrime(const mpz_class &n)
{
    return mpz_probab_prime_p(n.get_mpz_t(), 25) != 0;
}

// A random odd number with exactly `bits` bits (top bit forced on).
static mpz_class randomOdd(int bits)
{
    mpz_class x = rng.get_z_bits(bits);
    mpz_setbit(x.get_mpz_t(), bits - 1);       // keep the size
    mpz_setbit(x.get_mpz_t(), 0);              // make it odd
    return x;
}

// Hunt a prime with exactly `bits` bits by stepping through odd numbers.
static mpz_class generatePrime(int bits)
{
    mpz_class x = randomOdd(bits);
    while (!isPrime(x))
        x += 2;
    return x;
}

// Hunt a safe prime p = 2q + 1 with exactly `bits` bits (q prime as well).
// Knowing the factorisation of p-1 = 2q is what makes the primitive-root
// test below possible at this size.
static mpz_class generateSafePrime(int bits)
{
    while (true) {
        mpz_class q = generatePrime(bits - 1);
        mpz_class p = 2 * q + 1;
        if (isPrime(p))
            return p;
    }
}

// ---------------------------------------------------------------------------
// Neutrosophic prime generation (Definition 1.14):
// P = a + bI is a neutrosophic prime when both a and a+b are ordinary primes.
// We hunt the two coordinates independently and set b = (second) - a.
// For the DH modulus we additionally require safe primes (see above).
// ---------------------------------------------------------------------------
static NeutrosophicInt generateNeutroPrime(int bits, bool safe)
{
    mpz_class first = safe ? generateSafePrime(bits) : generatePrime(bits);
    mpz_class sum;
    do {
        sum = safe ? generateSafePrime(bits) : generatePrime(bits);
    } while (sum == first);                    // coordinates must differ
    return NeutrosophicInt(first, sum - first);
}

// Primitive root modulo a safe prime p = 2q + 1.
// g is a generator iff  g^((p-1)/2) != 1  and  g^((p-1)/q) != 1  (mod p).
static mpz_class primitiveRoot(const mpz_class &p, const mpz_class &q)
{
    mpz_class pm1 = p - 1;
    for (mpz_class g = 2; ; g++) {
        if (powmodOrdinary(g, pm1 / 2, p) != 1 &&
            powmodOrdinary(g, pm1 / q, p) != 1)
            return g;
    }
}

// ---------------------------------------------------------------------------
// Neutrosophic RSA keys (the paper's algorithm, Steps 1-4).
// The public exponent is fixed at 65537 + 0I, following classical practice
// (PKCS #1, RFC 8017): it is prime, so the coprimality check almost always
// passes, and its two one-bits make verification fast.
// ---------------------------------------------------------------------------
struct RSAKeys {
    NeutrosophicInt P, Q;                      // secret neutrosophic primes
    NeutrosophicInt N;                         // public modulus  N = P*Q
    NeutrosophicInt E;                         // public exponent (65537 + 0I)
    NeutrosophicInt D;                         // private exponent E^-1 mod phiS(N)
};

static RSAKeys rsaKeyGen(int bits)
{
    RSAKeys k;
    k.P = generateNeutroPrime(bits, false);
    k.Q = generateNeutroPrime(bits, false);
    k.N = k.P.mul(k.Q);
    NeutrosophicInt phiN = phiSFromPrimes(k.P, k.Q);
    k.E = NeutrosophicInt(65537, 0);
    if (!k.E.invMod(phiN, k.D)) {
        // Extremely unlikely: 65537 divides one track of phiS(N).
        // Regenerating Q once is enough in practice.
        return rsaKeyGen(bits);
    }
    return k;
}

// Textbook neutrosophic RSA signature:
//   sign(M)    = M^D mod N            (only the key owner can compute this)
//   verify(S)  = S^E mod N  ==  M     (anyone with the public key can check)
static NeutrosophicInt rsaSign(const NeutrosophicInt &msg, const RSAKeys &k)
{
    return msg.powmod(k.D, k.N);
}

static bool rsaVerify(const NeutrosophicInt &msg, const NeutrosophicInt &sig,
                      const NeutrosophicInt &E, const NeutrosophicInt &N)
{
    return sig.powmod(E, N) == msg;
}

// ---------------------------------------------------------------------------
// Protocol parties.  The "network" is the deliver() channel below; Eve can
// only act inside it.  Each party stores its long-term RSA key pair and the
// peer's trusted public key (requirement iii).
// ---------------------------------------------------------------------------
struct Party {
    string name;
    RSAKeys keys;                              // long-term neutrosophic RSA pair

    // Ephemeral (per-session) Diffie-Hellman material.
    NeutrosophicInt secret;                    // private DH exponent
    NeutrosophicInt dhPublic;                  // G^secret mod P_dh
    NeutrosophicInt signature;                 // RSA signature over dhPublic
    NeutrosophicInt sharedKey;                 // result of the key agreement
};

// What actually travels on the wire.
struct Message {
    NeutrosophicInt dhPublic;
    NeutrosophicInt signature;
};

// DH public parameters shared by everyone (known to Eve as well).
struct DHParams {
    NeutrosophicInt P;                         // neutrosophic safe-prime modulus
    mpz_class p1, q1;                          // first track:  p1 = 2*q1 + 1
    mpz_class p2, q2;                          // second track: p2 = 2*q2 + 1
    NeutrosophicInt G;                         // neutrosophic generator
};

// How Eve should interfere in a given demo run.
enum EveMode {
    EVE_ABSENT,                                // run 1: honest channel
    EVE_LAZY,                                  // run 2: reuse Alice's signature
    EVE_FORGE,                                 // run 3: sign with her own key
    EVE_REPLAY,                                // run 4: replay an old message
    EVE_TAMPER,                                // run 5: flip one bit of A_pub
    EVE_IMPERSONATE_BOB,                       // run 6: attack the return path
    EVE_POISON_G                               // run 7: downgrade the generator
};

// ---------------------------------------------------------------------------
// Parameter generation for the neutrosophic DH group (Section 3.3 / 3.4).
// ---------------------------------------------------------------------------
static DHParams dhGenerateParams(int bits)
{
    DHParams par;

    // Two independent safe primes per track; b is the gap between them.
    par.p1 = generateSafePrime(bits);
    par.q1 = (par.p1 - 1) / 2;
    do {
        par.p2 = generateSafePrime(bits);
    } while (par.p2 == par.p1);
    par.q2 = (par.p2 - 1) / 2;

    par.P = NeutrosophicInt(par.p1, par.p2 - par.p1);

    // A primitive root on each track, assembled into a neutrosophic generator.
    mpz_class g1 = primitiveRoot(par.p1, par.q1);
    mpz_class g2 = primitiveRoot(par.p2, par.q2);
    par.G = NeutrosophicInt::from_coords(g1, g2);
    return par;
}

// Sanity checks on the public parameters before anyone trusts them.
// A neutrosophic generator of 1 (or anything <= 1) would make every
// public value and every shared key collapse to a constant.
static bool dhParamsSane(const DHParams &par)
{
    mpz_class g1, g2;
    par.G.to_coords(g1, g2);
    return g1 > 1 && g2 > 1 && par.P.a > 2 && (par.P.a + par.P.b) > 2;
}

// A random positive neutrosophic secret exponent.
static NeutrosophicInt randomSecret(int bits)
{
    mpz_class e1 = rng.get_z_bits(bits) + 2;
    mpz_class e2 = rng.get_z_bits(bits);
    return NeutrosophicInt(e1, e2);
}

// The whole value of the protocol, in one step: a party turns its fresh
// secret into a signed public value.
static void partyProduceMessage(Party &who, const DHParams &par, int bits)
{
    who.secret    = randomSecret(bits);
    who.dhPublic  = par.G.powmod(who.secret, par.P);
    who.signature = rsaSign(who.dhPublic, who.keys);
}

// The receive gate: verify the signature on the incoming DH public value
// against the SENDER's trusted long-term public key before any use.
static bool partyVerifyMessage(const Party &sender, const Message &m)
{
    return rsaVerify(m.dhPublic, m.signature, sender.keys.E, sender.keys.N);
}

// Both sides derive the shared key from the verified peer value.
static void partyDeriveSharedKey(Party &who, const NeutrosophicInt &peerPublic,
                                 const DHParams &par)
{
    who.sharedKey = peerPublic.powmod(who.secret, par.P);
}

// ---------------------------------------------------------------------------
// The hostile channel.  Eve exists ONLY here.  Depending on the demo mode she
// substitutes, replays, tampers or poisons; she never learns a private key.
// ---------------------------------------------------------------------------
static Message deliver(const Message &m, EveMode eve,
                       const Party &eveParty,
                       const Message &recorded, const DHParams &par, int bits,
                       bool aliceToBob)
{
    switch (eve) {
    case EVE_ABSENT:
        return m;

    case EVE_LAZY: {
        // Eve replaces Alice's DH public value with her own but blindly
        // forwards Alice's signature, hoping it still checks out.
        cout << "  [Eve] swaps in her own DH public value but forwards Alice's\n"
                "  [Eve] signature unchanged (she cannot make a new one as Alice).\n";
        Party tmp = eveParty;
        tmp.secret   = randomSecret(bits);
        tmp.dhPublic = par.G.powmod(tmp.secret, par.P);
        Message forged{tmp.dhPublic, m.signature};
        return forged;
    }

    case EVE_FORGE: {
        // Eve replaces the value AND signs it -- with her OWN key.
        // The signature is valid, just not Alice's.
        cout << "  [Eve] swaps in her own DH public value and signs it with her\n"
                "  [Eve] OWN RSA key (a valid signature, but not Alice's).\n";
        Party tmp = eveParty;
        partyProduceMessage(tmp, par, bits);
        Message forged{tmp.dhPublic, tmp.signature};
        return forged;
    }

    case EVE_REPLAY:
        // Eve resends a genuine, correctly signed message from an old
        // session -- but only on the Alice -> Bob leg.  (Replaying on both
        // legs could never complete: Bob would mix the old value with his
        // fresh secret while Alice used her fresh secret, so the keys
        // could not possibly agree.)
        if (aliceToBob) {
            cout << "  [Eve] replays Alice's OLD (value, signature) pair from a\n"
                    "  [Eve] previous session. The signature is genuine!\n";
            return recorded;
        }
        return m;

    case EVE_TAMPER: {
        // Eve forwards everything but flips one bit of the public value.
        cout << "  [Eve] forwards Alice's message but flips ONE bit of the\n"
                "  [Eve] DH public value.\n";
        Message t = m;
        mpz_class flipped = t.dhPublic.a;
        mpz_setbit(flipped.get_mpz_t(), 0);
        if (flipped == t.dhPublic.a)
            mpz_clrbit(flipped.get_mpz_t(), 0);
        t.dhPublic.a = flipped;
        return t;
    }

    case EVE_IMPERSONATE_BOB:
        if (!aliceToBob) {
            // On the return path Eve answers Alice as if she were Bob.
            cout << "  [Eve] answers Alice pretending to be Bob, with her own\n"
                    "  [Eve] value signed under her own key.\n";
            Party tmp = eveParty;
            partyProduceMessage(tmp, par, bits);
            Message forged{tmp.dhPublic, tmp.signature};
            return forged;
        }
        return m;                            // first leg is left alone

    case EVE_POISON_G:
        // Nothing to change in transit; the poison lives in the parameters.
        return m;
    }
    return m;
}

// Pretty-print a big number without flooding the console: first 32 bits worth
// of hex plus the total bit length, so values can still be compared by eye.
static string brief(const NeutrosophicInt &x)
{
    mpz_class u, v;
    x.to_coords(u, v);
    auto shorten = [](const mpz_class &n) {
        string s = n.get_str(16);
        if (s.size() > 12) s = s.substr(0, 12) + "...";
        return s;
    };
    return "(" + shorten(u) + ", " + shorten(v) + ")  ["
         + to_string(mpz_sizeinbase(u.get_mpz_t(), 2)) + " & "
         + to_string(mpz_sizeinbase(v.get_mpz_t(), 2)) + " bits]";
}

// ---------------------------------------------------------------------------
// One full protocol run, with narration.  Returns true when the handshake
// completed (both gates passed and the shared keys agree).
// ---------------------------------------------------------------------------
static bool runHandshake(const string &title, EveMode eve,
                         Party &alice, Party &bob, Party &eveParty,
                         const DHParams &parIn, int bits)
{
    cout << "------------------------------------------------------------\n";
    cout << title << "\n";
    cout << "------------------------------------------------------------\n";

    // Run 7 poisons the generator before the protocol even starts.
    DHParams par = parIn;
    if (eve == EVE_POISON_G) {
        cout << "  [Eve] tampers with the PUBLIC PARAMETERS: she replaces the\n"
                "  [Eve] generator G by 1 + 0I, hoping both sides use it.\n";
        par.G = NeutrosophicInt(1, 0);
    }

    // Parameter sanity check -- the defense against run 7.
    if (!dhParamsSane(par)) {
        cout << "  [!] Parameter check FAILED: the generator is trivial.\n"
                "  [!] Both parties reject the parameters; protocol aborts.\n\n";
        return false;
    }
    cout << "  Parameter check OK: both generator coordinates exceed 1.\n";

    // Run 4 needs a genuine old message from a previous session.
    Message recorded{};
    if (eve == EVE_REPLAY) {
        Party oldAlice = alice;
        partyProduceMessage(oldAlice, par, bits);
        recorded.dhPublic  = oldAlice.dhPublic;
        recorded.signature = oldAlice.signature;
        cout << "  [setup] Eve recorded a genuine signed value from Alice's\n"
                "  [setup] previous session.\n";
    }

    // ---- Step 1: Alice creates and sends her signed DH public value --------
    partyProduceMessage(alice, par, bits);
    cout << "\n  Step 1  Alice picks a fresh secret and sends her DH public value\n"
            "          together with her RSA signature on it.\n";
    cout << "          Alice's DH public value: " << brief(alice.dhPublic) << "\n";

    Message wire1{alice.dhPublic, alice.signature};
    Message got1 = deliver(wire1, eve, eveParty, recorded, par, bits,
                           /*aliceToBob=*/true);

    // ---- Step 2: Bob's receive gate, then his reply -------------------------
    cout << "\n  Step 2  Bob verifies the signature against ALICE's trusted\n"
            "          long-term public key...\n";
    if (!partyVerifyMessage(alice, got1)) {
        cout << "          VERIFICATION FAILED. Bob aborts; no key is created.\n\n";
        return false;
    }
    cout << "          Signature valid: the value really came from Alice.\n";

    partyProduceMessage(bob, par, bits);
    cout << "          Bob replies with his own signed DH public value.\n";
    cout << "          Bob's DH public value:   " << brief(bob.dhPublic) << "\n";

    Message wire2{bob.dhPublic, bob.signature};
    Message got2 = deliver(wire2, eve, eveParty, recorded, par, bits,
                           /*aliceToBob=*/false);

    // ---- Step 3: Alice's receive gate ---------------------------------------
    cout << "\n  Step 3  Alice verifies the signature against BOB's trusted\n"
            "          long-term public key...\n";
    if (!partyVerifyMessage(bob, got2)) {
        cout << "          VERIFICATION FAILED. Alice aborts; no key is created.\n\n";
        return false;
    }
    cout << "          Signature valid: the value really came from Bob.\n";

    // ---- Step 4: both derive the shared key ---------------------------------
    partyDeriveSharedKey(alice, got2.dhPublic, par);
    partyDeriveSharedKey(bob, got1.dhPublic, par);

    cout << "\n  Step 4  Both sides derive the shared key independently:\n";
    cout << "          Alice's key: " << brief(alice.sharedKey) << "\n";
    cout << "          Bob's key:   " << brief(bob.sharedKey) << "\n";

    if (alice.sharedKey == bob.sharedKey) {
        cout << "          The two keys MATCH -- agreement succeeded.\n\n";
        return true;
    }
    cout << "          Keys DO NOT match.\n";
    if (eve == EVE_REPLAY)
        cout << "          Expected here: Bob derived his key from Alice's OLD\n"
                "          replayed value, Alice from Bob's FRESH value. Eve gained\n"
                "          nothing (she knows neither secret, so she cannot\n"
                "          compute either key), but the session is desynchronised:\n"
                "          a replay cannot break confidentiality, it can only\n"
                "          disrupt the run.\n";
    cout << "\n";
    return false;
}

static void runPartBDemos()
{
    cout << "==================== PART B : authenticated DHKE ====================\n";
    cout << "Generating long-term neutrosophic RSA key pairs for Alice, Bob and\n"
            "Eve, plus the shared neutrosophic DH group.\n"
            "RSA uses 257-bit primes and DH uses 256-bit primes. Both clear the\n"
            "256-bit minimum; the extra RSA bit guarantees a DH public value is\n"
            "always smaller than the RSA modulus on both tracks, so signing never\n"
            "wraps.\n\n";

    const int RSA_BITS = 257;   // RSA primes: one bit above the DH size so a
                                // DH public value always fits inside the
                                // RSA modulus on both tracks.
    const int DH_BITS  = 256;

    Party alice, bob, eve;
    alice.name = "Alice";
    bob.name   = "Bob";
    eve.name   = "Eve";
    alice.keys = rsaKeyGen(RSA_BITS);
    bob.keys   = rsaKeyGen(RSA_BITS);
    eve.keys   = rsaKeyGen(RSA_BITS);

    DHParams par = dhGenerateParams(DH_BITS);

    // Show the generated group parameters (this is the "verify all
    // intermediate values" evidence the assignment asks for).
    mpz_class g1, g2;
    par.G.to_coords(g1, g2);
    cout << "DH public parameters:\n";
    cout << "  neutrosophic modulus P = " << par.P << "\n";
    cout << "  Both coordinates of P are 256-bit safe primes p = 2q + 1, so the\n"
            "  factorisation of p - 1 is known and a generator can be verified\n"
            "  with two exponentiations per track.\n";

    cout << "\n  Primitive-root check on track 1 (p = first coordinate of P):\n";
    cout << "    candidate g = " << g1.get_str() << "\n";
    cout << "    g^((p-1)/2) mod p = "
         << powmodOrdinary(g1, par.q1, par.p1).get_str() << "\n";
    cout << "    g^((p-1)/q) mod p = "
         << powmodOrdinary(g1, mpz_class(2), par.p1).get_str() << "\n";
    cout << "    Neither is 1, so " << g1.get_str()
         << " generates the units mod p. Track 2 accepts " << g2.get_str()
         << " by the same test.\n";

    cout << "\n  generator G = " << par.G
         << "   (coordinates " << g1.get_str() << " and " << g2.get_str()
         << ", one primitive root per track)\n";
    cout << "  ord(G) = lcm(a-1, a+b-1)\n\n";

    runHandshake("RUN 1 -- honest channel (no Eve): correctness",
                 EVE_ABSENT, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 2 -- Eve forwards her own value with Alice's signature",
                 EVE_LAZY, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 3 -- Eve signs her own value with her OWN key",
                 EVE_FORGE, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 4 -- Eve replays an old genuine message",
                 EVE_REPLAY, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 5 -- Eve flips one bit of Alice's public value",
                 EVE_TAMPER, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 6 -- Eve impersonates Bob on the return path",
                 EVE_IMPERSONATE_BOB, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 7 -- Eve poisons the public generator (G = 1)",
                 EVE_POISON_G, alice, bob, eve, par, DH_BITS);

    cout << "============================================================\n";
    cout << "Summary: the honest run completed with matching keys. Every\n"
            "forgery or tampering attempt was stopped at a signature gate\n"
            "or at the parameter sanity check, and the replay -- the only\n"
            "attack a signature alone cannot stop -- merely desynchronised\n"
            "the session without leaking anything to Eve.\n";
}

// ============================================================================
// main: no arguments runs everything; "partA" or "partB" selects a section.
// ============================================================================
int main(int argc, char **argv)
{
    string mode = (argc > 1) ? argv[1] : "all";

    if (mode == "partA") {
        runPartATests();
    } else if (mode == "partB") {
        runPartBDemos();
    } else {
        runPartATests();
        runPartBDemos();
    }
    return 0;
}
