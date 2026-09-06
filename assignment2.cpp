// ============================================================================
// SIL7159: Cryptography and Cryptanalysis, Assignment 2
//
// Build:  g++ -O2 assignment2.cpp -lgmpxx -lgmp -o assignment2
// Run:    ./assignment2            (Part A tests, then the Part B demos)
//         ./assignment2 partA      (Part A only)
//         ./assignment2 partB      (Part B only)
// ============================================================================

#include <gmpxx.h>
#include <iostream>
#include <string>

using namespace std;

// Fixed seed so every run produces the same keys and the same console
// output. Change this constant for a fresh set of values.
static gmp_randclass rng(gmp_randinit_mt);

static void seedRng()
{
    rng.seed(mpz_class("12345678901234567890"));
}

// ============================================================================
//
//                                  PART A
//
// ============================================================================

static mpz_class gcdPlain(mpz_class x, mpz_class y)
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

static mpz_class powModPlain(mpz_class base, mpz_class exp, const mpz_class &m)
{
    base %= m;
    if (base < 0) base += m;
    mpz_class result = 1;
    while (exp > 0) {
        if (mpz_odd_p(exp.get_mpz_t()))
            result = (result * base) % m;
        base = (base * base) % m;
        exp >>= 1;
    }
    return result;
}

// Writes e^-1 mod m into inv and returns true, or returns false when
// gcd(e, m) != 1 and no inverse exists.
static bool invModPlain(const mpz_class &e, const mpz_class &m, mpz_class &inv)
{
    if (gcdPlain(e, m) != 1)
        return false;

    mpz_class rOld = e % m, r = m;
    mpz_class sOld = 1,     s = 0;
    while (r != 0) {
        mpz_class q = rOld / r;
        mpz_class tmp;

        tmp = rOld - q * r;  rOld = r;  r = tmp;
        tmp = sOld - q * s;  sOld = s;  s = tmp;
    }
    inv = sOld % m;
    if (inv < 0) inv += m;
    return true;
}

static mpz_class phiPlain(const mpz_class &n)
{
    mpz_class result = n;
    mpz_class rest = n;
    for (mpz_class p = 2; p * p <= rest; p++) {
        if (rest % p == 0) {
            result -= result / p;
            while (rest % p == 0)
                rest /= p;
        }
    }
    if (rest > 1)
        result -= result / rest;
    return result;
}

struct NeutrosophicInt {
    mpz_class a;
    mpz_class b;

    NeutrosophicInt(const mpz_class &a_ = 0, const mpz_class &b_ = 0)
        : a(a_), b(b_) {}

    void toCoords(mpz_class &u, mpz_class &v) const {
        u = a;
        v = a + b;
    }
    static NeutrosophicInt fromCoords(const mpz_class &u, const mpz_class &v) {
        return NeutrosophicInt(u, v - u);
    }

    NeutrosophicInt add(const NeutrosophicInt &o) const {
        return NeutrosophicInt(a + o.a, b + o.b);
    }

    NeutrosophicInt mul(const NeutrosophicInt &o) const {
        mpz_class first = a * o.a;
        mpz_class sums  = (a + b) * (o.a + o.b);
        return NeutrosophicInt(first, sums - first);
    }

    bool isCoprime(const NeutrosophicInt &o) const {
        return gcdPlain(a, o.a) == 1
            && gcdPlain(a + b, o.a + o.b) == 1;
    }

    NeutrosophicInt phiS() const {
        mpz_class p1 = phiPlain(a);
        mpz_class p2 = phiPlain(a + b);
        return NeutrosophicInt(p1, p2 - p1);
    }

    NeutrosophicInt powMod(const NeutrosophicInt &exponent,
                           const NeutrosophicInt &modulus) const {
        mpz_class t1 = powModPlain(a,     exponent.a,
                                   modulus.a);
        mpz_class t2 = powModPlain(a + b, exponent.a + exponent.b,
                                   modulus.a + modulus.b);
        return fromCoords(t1, t2);
    }

    bool invMod(const NeutrosophicInt &modulus, NeutrosophicInt &result) const {
        mpz_class s1, sSum;
        if (!invModPlain(a,     modulus.a,               s1))   return false;
        if (!invModPlain(a + b, modulus.a + modulus.b,   sSum)) return false;
        result = fromCoords(s1, sSum);
        return true;
    }

    bool operator==(const NeutrosophicInt &o) const {
        return a == o.a && b == o.b;
    }
};

static ostream &operator<<(ostream &out, const NeutrosophicInt &x)
{
    out << x.a.get_str() << " + (" << x.b.get_str() << ")I";
    return out;
}

// Part B needs phiS(N) for N = P*Q where P and Q are known neutrosophic
// primes. Trial division is not an option at 257 bits, but it does not
// need to be: for a prime coordinate phi is "subtract one", so
// phiS(P) = (a-1) + bI and phiS(P*Q) = phiS(P) * phiS(Q).
static NeutrosophicInt phiSFromPrimes(const NeutrosophicInt &P,
                                      const NeutrosophicInt &Q)
{
    NeutrosophicInt phiP(P.a - 1, P.b);
    NeutrosophicInt phiQ(Q.a - 1, Q.b);
    return phiP.mul(phiQ);
}

static int failures = 0;

static void check(const string &name, bool ok)
{
    cout << (ok ? "PASS  " : "FAIL  ") << name << "\n";
    if (!ok) failures++;
}

static void runPartATests()
{
    cout << "==================== PART A: unit tests ====================\n";

    {
        NeutrosophicInt x(3, 2);
        mpz_class u, v;
        x.toCoords(u, v);
        check("A.1 toCoords: 3+2I -> (3,5)", u == 3 && v == 5);

        NeutrosophicInt back = NeutrosophicInt::fromCoords(7, 12);
        check("A.1 fromCoords: (7,12) -> 7+5I", back.a == 7 && back.b == 5);
    }

    {
        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.2 add: (3+2I)+(5+6I) = 8+8I",
              A.add(B) == NeutrosophicInt(8, 8));

        NeutrosophicInt C(4, -3), D(1, 5);
        check("A.2 add: (4-3I)+(1+5I) = 5+2I",
              C.add(D) == NeutrosophicInt(5, 2));
    }

    {
        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.3 mul: (3+2I)(5+6I) = 15+40I",
              A.mul(B) == NeutrosophicInt(15, 40));

        NeutrosophicInt P(3, 2), Q(7, 4);
        check("A.3 mul: (3+2I)(7+4I) = 21+34I",
              P.mul(Q) == NeutrosophicInt(21, 34));
    }

    {
        NeutrosophicInt P(3, 2), Q(7, 4);
        check("A.4 isCoprime: (3+2I, 7+4I) coprime", P.isCoprime(Q));

        NeutrosophicInt X(2, 2), Y(4, 4);
        check("A.4 isCoprime: (2+2I, 4+4I) not coprime", !X.isCoprime(Y));
    }

    {
        NeutrosophicInt AB(15, 40);
        check("A.5 phiS: phiS(15+40I) = 8+32I",
              AB.phiS() == NeutrosophicInt(8, 32));

        NeutrosophicInt N(21, 34);
        check("A.5 phiS: phiS(21+34I) = 12+28I",
              N.phiS() == NeutrosophicInt(12, 28));

        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.5 phiS: same answer via the prime factors of 15+40I",
              AB.phiS() == phiSFromPrimes(A, B));
    }

    {
        NeutrosophicInt M(3, 3), E(5, 6), N(21, 34);
        check("A.6 powMod: (3+3I)^(5+6I) mod (21+34I) = 12-6I",
              M.powMod(E, N) == NeutrosophicInt(12, -6));

        NeutrosophicInt M2(2, 6), E2(17, 14), N2(91, 116);
        check("A.6 powMod: (2+6I)^(17+14I) mod (91+116I) = 32+138I",
              M2.powMod(E2, N2) == NeutrosophicInt(32, 138));
    }

    {
        NeutrosophicInt E(5, 6), phiN(12, 28), inv;
        bool ok = E.invMod(phiN, inv);
        check("A.7 invMod: (5+6I)^-1 mod (12+28I) = 5+6I",
              ok && inv == NeutrosophicInt(5, 6));

        NeutrosophicInt E2(17, 14), phiN2(72, 108), inv2;
        bool ok2 = E2.invMod(phiN2, inv2);
        check("A.7 invMod: (17+14I)^-1 mod (72+108I) = 17+134I",
              ok2 && inv2 == NeutrosophicInt(17, 134));

        NeutrosophicInt prod = E.mul(inv);
        mpz_class t1 = prod.a % phiN.a;
        mpz_class t2 = (prod.a + prod.b) % (phiN.a + phiN.b);
        check("A.7 invMod: E times its inverse gives 1 on both tracks",
              t1 == 1 && t2 == 1);
    }

    {
        NeutrosophicInt M(3, 3), E(5, 6), N(21, 34);
        NeutrosophicInt C = M.powMod(E, N);
        NeutrosophicInt phiN(12, 28), D;
        E.invMod(phiN, D);
        NeutrosophicInt back = C.powMod(D, N);
        check("RSA round-trip: decrypt(encrypt(3+3I)) = 3+3I", back == M);
    }

    cout << (failures == 0 ? "All Part A tests passed.\n"
                           : "Some Part A tests FAILED.\n");
    cout << "\n";
}

// ============================================================================
//
//                                  PART B
//
// ============================================================================

static bool isPrime(const mpz_class &n)
{
    return mpz_probab_prime_p(n.get_mpz_t(), 25) != 0;
}

static mpz_class randomOdd(int bits)
{
    mpz_class x = rng.get_z_bits(bits);
    mpz_setbit(x.get_mpz_t(), bits - 1);
    mpz_setbit(x.get_mpz_t(), 0);
    return x;
}

static mpz_class generatePrime(int bits)
{
    mpz_class x = randomOdd(bits);
    while (!isPrime(x))
        x += 2;
    return x;
}

// A safe prime p = 2q + 1. We need p - 1 factored to test generators, and
// this construction hands us the factorisation (2 and q) for free.
static mpz_class generateSafePrime(int bits)
{
    while (true) {
        mpz_class q = generatePrime(bits - 1);
        mpz_class p = 2 * q + 1;
        if (isPrime(p))
            return p;
    }
}

static NeutrosophicInt generateNeutroPrime(int bits, bool safe)
{
    mpz_class first = safe ? generateSafePrime(bits) : generatePrime(bits);
    mpz_class sum;
    do {
        sum = safe ? generateSafePrime(bits) : generatePrime(bits);
    } while (sum == first);
    return NeutrosophicInt(first, sum - first);
}

// g generates the units mod a safe prime p = 2q+1 iff neither
// g^((p-1)/2) nor g^((p-1)/q) is 1 mod p. Small g values pass quickly.
static mpz_class primitiveRoot(const mpz_class &p, const mpz_class &q)
{
    mpz_class pm1 = p - 1;
    for (mpz_class g = 2; ; g++) {
        if (powModPlain(g, pm1 / 2, p) != 1 &&
            powModPlain(g, pm1 / q, p) != 1)
            return g;
    }
}

struct RSAKeys {
    NeutrosophicInt P, Q;
    NeutrosophicInt N;
    NeutrosophicInt E;
    NeutrosophicInt D;
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
        // 65537 divided one coordinate of phiS(N). Regenerate.
        return rsaKeyGen(bits);
    }
    return k;
}

static NeutrosophicInt rsaSign(const NeutrosophicInt &msg, const RSAKeys &k)
{
    return msg.powMod(k.D, k.N);
}

static bool rsaVerify(const NeutrosophicInt &msg, const NeutrosophicInt &sig,
                      const NeutrosophicInt &E, const NeutrosophicInt &N)
{
    return sig.powMod(E, N) == msg;
}

struct Party {
    string name;
    RSAKeys keys;
    NeutrosophicInt secret;
    NeutrosophicInt dhPublic;
    NeutrosophicInt signature;
    NeutrosophicInt sharedKey;
};

struct Message {
    NeutrosophicInt dhPublic;
    NeutrosophicInt signature;
};

struct DHParams {
    NeutrosophicInt P;
    mpz_class p1, q1;
    mpz_class p2, q2;
    NeutrosophicInt G;
};

enum EveMode {
    EVE_ABSENT,
    EVE_LAZY,
    EVE_FORGE,
    EVE_REPLAY,
    EVE_TAMPER,
    EVE_IMPERSONATE_BOB,
    EVE_POISON_G
};

static DHParams dhGenerateParams(int bits)
{
    DHParams par;

    par.p1 = generateSafePrime(bits);
    par.q1 = (par.p1 - 1) / 2;
    do {
        par.p2 = generateSafePrime(bits);
    } while (par.p2 == par.p1);
    par.q2 = (par.p2 - 1) / 2;

    par.P = NeutrosophicInt(par.p1, par.p2 - par.p1);

    mpz_class g1 = primitiveRoot(par.p1, par.q1);
    mpz_class g2 = primitiveRoot(par.p2, par.q2);
    par.G = NeutrosophicInt::fromCoords(g1, g2);
    return par;
}

// A generator of 1 would collapse every public value and every key to 1,
// so both sides reject trivial parameters before doing anything else.
static bool dhParamsSane(const DHParams &par)
{
    mpz_class g1, g2;
    par.G.toCoords(g1, g2);
    return g1 > 1 && g2 > 1 && par.P.a > 2 && (par.P.a + par.P.b) > 2;
}

static NeutrosophicInt randomSecret(int bits)
{
    mpz_class e1 = rng.get_z_bits(bits) + 2;
    mpz_class e2 = rng.get_z_bits(bits);
    return NeutrosophicInt(e1, e2);
}

static void partyProduceMessage(Party &who, const DHParams &par, int bits)
{
    who.secret    = randomSecret(bits);
    who.dhPublic  = par.G.powMod(who.secret, par.P);
    who.signature = rsaSign(who.dhPublic, who.keys);
}

static bool partyVerifyMessage(const Party &sender, const Message &m)
{
    return rsaVerify(m.dhPublic, m.signature, sender.keys.E, sender.keys.N);
}

static void partyDeriveSharedKey(Party &who, const NeutrosophicInt &peerPublic,
                                 const DHParams &par)
{
    who.sharedKey = peerPublic.powMod(who.secret, par.P);
}

static Message deliver(const Message &m, EveMode eve,
                       const Party &eveParty,
                       const Message &recorded, const DHParams &par, int bits,
                       bool aliceToBob)
{
    switch (eve) {
    case EVE_ABSENT:
        return m;

    case EVE_LAZY: {
        cout << "  Eve replaces Alice's DH public value with her own but keeps\n"
                "  Alice's signature, since she cannot produce a new one as Alice.\n";
        Party tmp = eveParty;
        tmp.secret   = randomSecret(bits);
        tmp.dhPublic = par.G.powMod(tmp.secret, par.P);
        Message forged{tmp.dhPublic, m.signature};
        return forged;
    }

    case EVE_FORGE: {
        cout << "  Eve replaces Alice's DH public value with her own and signs\n"
                "  it with her own RSA key. The signature is genuine, but it is hers.\n";
        Party tmp = eveParty;
        partyProduceMessage(tmp, par, bits);
        Message forged{tmp.dhPublic, tmp.signature};
        return forged;
    }

    case EVE_REPLAY:
        // Replay on one leg only. On both legs the run could never agree:
        // Bob would mix the old public value with his fresh secret while
        // Alice used her fresh secret.
        if (aliceToBob) {
            cout << "  Eve replays the old DH public value and signature she\n"
                    "  recorded. The signature is genuine, so it passes the gate.\n";
            return recorded;
        }
        return m;

    case EVE_TAMPER: {
        cout << "  Eve passes the message along but flips one bit of Alice's\n"
                "  DH public value first.\n";
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
            cout << "  Eve answers Alice as if she were Bob, sending her own\n"
                    "  DH public value signed with her own key.\n";
            Party tmp = eveParty;
            partyProduceMessage(tmp, par, bits);
            Message forged{tmp.dhPublic, tmp.signature};
            return forged;
        }
        return m;

    case EVE_POISON_G:
        return m;
    }
    return m;
}

static bool runHandshake(const string &title, EveMode eve,
                         Party &alice, Party &bob, Party &eveParty,
                         const DHParams &parIn, int bits)
{
    cout << "------------------------------------------------------------\n";
    cout << title << "\n";
    cout << "------------------------------------------------------------\n";

    DHParams par = parIn;
    if (eve == EVE_POISON_G) {
        cout << "  Eve gets to the shared parameters first and replaces the\n"
                "  generator with 1 + 0I.\n";
        par.G = NeutrosophicInt(1, 0);
    }

    if (!dhParamsSane(par)) {
        cout << "  The generator is trivial, so both sides reject the\n"
                "  parameters and the protocol stops before it starts.\n\n";
        return false;
    }
    cout << "  Parameter check passed: both generator coordinates exceed 1.\n";

    Message recorded{};
    if (eve == EVE_REPLAY) {
        Party oldAlice = alice;
        partyProduceMessage(oldAlice, par, bits);
        recorded.dhPublic  = oldAlice.dhPublic;
        recorded.signature = oldAlice.signature;
        cout << "  Before this run, Eve recorded one of Alice's old signed\n"
                "  DH public values from an earlier session.\n";
    }

    partyProduceMessage(alice, par, bits);
    cout << "\n  Step 1  Alice picks a fresh secret, computes her DH public\n"
            "          value, and signs it with her RSA key.\n";
    cout << "          DH public value = " << alice.dhPublic << "\n";
    cout << "          signature       = " << alice.signature << "\n";

    Message wire1{alice.dhPublic, alice.signature};
    Message got1 = deliver(wire1, eve, eveParty, recorded, par, bits,
                           /*aliceToBob=*/true);

    cout << "\n  Step 2  Bob checks the signature against Alice's long-term\n"
            "          public key, which he already trusts.\n";
    if (!partyVerifyMessage(alice, got1)) {
        cout << "          The signature does not match the DH public value.\n"
                "          Bob stops here and no key is created.\n\n";
        return false;
    }
    cout << "          It matches, so this DH public value really is Alice's.\n";

    partyProduceMessage(bob, par, bits);
    cout << "          Bob answers with his own signed DH public value.\n";
    cout << "          DH public value = " << bob.dhPublic << "\n";
    cout << "          signature       = " << bob.signature << "\n";

    Message wire2{bob.dhPublic, bob.signature};
    Message got2 = deliver(wire2, eve, eveParty, recorded, par, bits,
                           /*aliceToBob=*/false);

    cout << "\n  Step 3  Alice checks Bob's signature the same way.\n";
    if (!partyVerifyMessage(bob, got2)) {
        cout << "          The signature does not match the DH public value.\n"
                "          Alice stops here and no key is created.\n\n";
        return false;
    }
    cout << "          It matches, so this DH public value really is Bob's.\n";

    partyDeriveSharedKey(alice, got2.dhPublic, par);
    partyDeriveSharedKey(bob, got1.dhPublic, par);

    cout << "\n  Step 4  Each side derives the shared key on its own.\n";
    cout << "          Alice gets " << alice.sharedKey << "\n";
    cout << "          Bob gets   " << bob.sharedKey << "\n";

    if (alice.sharedKey == bob.sharedKey) {
        cout << "          The keys are identical. Agreement succeeded.\n\n";
        return true;
    }
    cout << "          The keys differ.\n";
    if (eve == EVE_REPLAY)
        cout << "          That is the expected damage here. Bob mixed his\n"
                "          fresh secret with Alice's old DH public value, Alice\n"
                "          mixed her fresh secret with Bob's new one, so the\n"
                "          two keys cannot agree. Eve still learns nothing: she\n"
                "          has neither secret, so she cannot compute either\n"
                "          key. A replay can disrupt a session but it cannot\n"
                "          expose it.\n";
    cout << "\n";
    return false;
}

static void runPartBDemos()
{
    cout << "==================== PART B: authenticated DHKE ====================\n";
    cout << "Generating RSA key pairs for Alice, Bob and Eve, plus the shared\n"
            "DH group. RSA uses 257-bit primes and DH uses 256-bit primes.\n"
            "Both clear the 256-bit floor, and the extra RSA bit guarantees\n"
            "a DH public value always fits inside the RSA modulus, so a\n"
            "signature never wraps around it.\n\n";

    const int RSA_BITS = 257;
    const int DH_BITS  = 256;

    Party alice, bob, eve;
    alice.name = "Alice";
    bob.name   = "Bob";
    eve.name   = "Eve";
    alice.keys = rsaKeyGen(RSA_BITS);
    bob.keys   = rsaKeyGen(RSA_BITS);
    eve.keys   = rsaKeyGen(RSA_BITS);

    DHParams par = dhGenerateParams(DH_BITS);

    mpz_class g1, g2;
    par.G.toCoords(g1, g2);
    cout << "DH public parameters:\n";
    cout << "  P = " << par.P << "\n";
    cout << "  Both coordinates of P are 256-bit safe primes p = 2q + 1.\n";
    cout << "\n";
    cout << "  Generator search, track 1:\n";
    cout << "    try g = " << g1.get_str() << "\n";
    cout << "    g^((p-1)/2) mod p = "
         << powModPlain(g1, par.q1, par.p1).get_str() << "\n";
    cout << "    g^((p-1)/q) mod p = "
         << powModPlain(g1, mpz_class(2), par.p1).get_str() << "\n";
    cout << "    Neither result is 1, so " << g1.get_str()
         << " generates the units mod p.\n";
    cout << "    Track 2 passes the same test with g = " << g2.get_str() << ".\n";
    cout << "\n";
    cout << "  G = " << par.G << "\n";

    mpz_class trackOrder1 = par.p1 - 1, trackOrder2 = par.p2 - 1, lg;
    mpz_gcd(lg.get_mpz_t(), trackOrder1.get_mpz_t(), trackOrder2.get_mpz_t());
    mpz_class ordG = trackOrder1 / lg * trackOrder2;
    cout << "  ord(G) = lcm(a-1, a+b-1) = " << ordG << "\n\n";

    runHandshake("RUN 1 -- no Eve on the line: a clean handshake",
                 EVE_ABSENT, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 2 -- Eve swaps in her own DH public value but keeps Alice's signature",
                 EVE_LAZY, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 3 -- Eve signs her own DH public value with her own key",
                 EVE_FORGE, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 4 -- Eve replays an old signed DH public value from Alice",
                 EVE_REPLAY, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 5 -- Eve flips one bit of Alice's DH public value",
                 EVE_TAMPER, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 6 -- Eve answers Alice pretending to be Bob",
                 EVE_IMPERSONATE_BOB, alice, bob, eve, par, DH_BITS);
    runHandshake("RUN 7 -- Eve replaces the shared generator with 1",
                 EVE_POISON_G, alice, bob, eve, par, DH_BITS);

    cout << "============================================================\n";
    cout << "Summary. The clean run went through with matching keys. Runs 2,\n"
            "3, 5 and 6 all died at a signature check, run 7 never got past\n"
            "the parameter check, and the replay in run 4 is the one case a\n"
            "signature cannot stop; even there Eve walks away with nothing,\n"
            "she only manages to break the session's agreement.\n";
}

int main(int argc, char **argv)
{
    string mode = (argc > 1) ? argv[1] : "all";

    seedRng();

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
