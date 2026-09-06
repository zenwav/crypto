// Build:  g++ -std=c++17 -O2 -Wall -Wextra -Wpedantic dhke.cpp -lgmpxx -lgmp -o dhke
// Run:    ./dhke            (Part A tests, then the Part B demos)

#include <gmpxx.h>
#include <iostream>
#include <string>

using namespace std;

// The fixed seed keeps coursework runs repeatable; it is not secure randomness.
gmp_randclass rng(gmp_randinit_mt);

void seedRng()
{
    rng.seed(mpz_class("12345678901234567890"));
}

// Part A

mpz_class ordinaryGcd(mpz_class x, mpz_class y) {
    if (x < 0) x = -x;
    if (y < 0) y = -y;

    while (y != 0) {
        mpz_class r = x % y;
        x = y;
        y = r;
    }

    return x;
}

mpz_class powModPlain(mpz_class base, mpz_class exp, const mpz_class &m) {
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

bool ordinaryModInv(const mpz_class &e, const mpz_class &m, mpz_class &inv) {
    if (m <= 1) return false;
    mpz_class reducedE = e % m;

    if (reducedE < 0) reducedE += m;

    if (ordinaryGcd(reducedE, m) != 1) return false;
    mpz_class rOld = reducedE, r = m;

    mpz_class sOld = 1, s = 0;

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

mpz_class phiPlain(const mpz_class &n) {
    mpz_class result = n;
    mpz_class rest = n;

    for (mpz_class p = 2; p * p <= rest; p++) {
        if (rest % p == 0) {
            result -= result / p;
            while (rest % p == 0) rest /= p;
        }
    }
    if (rest > 1) result -= result / rest;

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
        mpz_class sums = (a + b) * (o.a + o.b);
        return NeutrosophicInt(first, sums - first);
    }

    bool isCoprime(const NeutrosophicInt &o) const {
        return ordinaryGcd(a, o.a) == 1 && ordinaryGcd(a + b, o.a + o.b) == 1;
    }


    NeutrosophicInt phiS() const {
        mpz_class p1 = phiPlain(a);
        mpz_class p2 = phiPlain(a + b);
        return NeutrosophicInt(p1, p2 - p1);
    }

    NeutrosophicInt powMod(const NeutrosophicInt &exponent, const NeutrosophicInt &modulus) const {
        mpz_class t1 = powModPlain(a, exponent.a, modulus.a);
        mpz_class t2 = powModPlain(a + b, exponent.a + exponent.b, modulus.a + modulus.b);
        return fromCoords(t1, t2);
    }

    bool invMod(const NeutrosophicInt &modulus, NeutrosophicInt &result) const {
        mpz_class s1, sSum;
        if (!ordinaryModInv(a, modulus.a, s1)) return false;

        if (!ordinaryModInv(a + b, modulus.a + modulus.b, sSum)) return false;

        result = fromCoords(s1, sSum);
        return true;
    }

    bool operator==(const NeutrosophicInt &o) const {
        return a == o.a && b == o.b;
    }
};

ostream &operator<<(ostream &out, const NeutrosophicInt &x) {
    out << x.a.get_str() << " + (" << x.b.get_str() << ")I";
    return out;
}

// The prime factors are already known, so large values do not need trial division.
NeutrosophicInt phiSFromPrimes(const NeutrosophicInt &P, const NeutrosophicInt &Q) {
    NeutrosophicInt phiP(P.a - 1, P.b);
    NeutrosophicInt phiQ(Q.a - 1, Q.b);
    return phiP.mul(phiQ);
}

int failures = 0;

void check(const string &name, bool isOk) {
    cout << (isOk ? "PASS " : "FAIL ") << name << "\n";
    if (!isOk) failures++;
}

void partATests() {
    cout << "***** PART A tests *****\n";
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
        check("A.2 add: (3+2I)+(5+6I) = 8+8I", A.add(B) == NeutrosophicInt(8, 8));

        NeutrosophicInt C(4, -3), D(1, 5);
        check("A.2 add: (4-3I)+(1+5I) = 5+2I", C.add(D) == NeutrosophicInt(5, 2));
    }

    {
        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.3 mul: (3+2I)(5+6I) = 15+40I", A.mul(B) == NeutrosophicInt(15, 40));

        NeutrosophicInt P(3, 2), Q(7, 4);
        check("A.3 mul: (3+2I)(7+4I) = 21+34I", P.mul(Q) == NeutrosophicInt(21, 34));

        NeutrosophicInt C(2, 1), D(4, -1);
        check("A.3 mul: (2+I)(4-I) = 8+I", C.mul(D) == NeutrosophicInt(8, 1));
    }

    {
        NeutrosophicInt P(3, 2), Q(7, 4);
        check("A.4 isCoprime: (3+2I, 7+4I) coprime", P.isCoprime(Q));

        NeutrosophicInt X(2, 2), Y(4, 4);
        check("A.4 isCoprime: (2+2I, 4+4I) not coprime", !X.isCoprime(Y));
    }

    {
        NeutrosophicInt AB(15, 40);
        check("A.5 phiS: phiS(15+40I) = 8+32I", AB.phiS() == NeutrosophicInt(8, 32));

        NeutrosophicInt N(21, 34);
        check("A.5 phiS: phiS(21+34I) = 12+28I", N.phiS() == NeutrosophicInt(12, 28));

        NeutrosophicInt A(3, 2), B(5, 6);
        check("A.5 phiS: same answer via the prime factors of 15+40I", AB.phiS() == phiSFromPrimes(A, B));

        NeutrosophicInt myTest(8, 7);
        check("A.5 phiS: phiS(8+7I) = 4+4I", myTest.phiS() == NeutrosophicInt(4, 4));
    }

    {
        NeutrosophicInt M(3, 3), E(5, 6), N(21, 34);
        check("A.6 powMod: (3+3I)^(5+6I) mod (21+34I) = 12-6I", M.powMod(E, N) == NeutrosophicInt(12, -6));

        NeutrosophicInt M2(2, 6), E2(17, 14), N2(91, 116);
        check("A.6 powMod: (2+6I)^(17+14I) mod (91+116I) = 32+138I", M2.powMod(E2, N2) == NeutrosophicInt(32, 138));

        NeutrosophicInt M3(2, 1), E3(4, 1), N3(11, 2);
        check("A.6 powMod: (2+I)^(4+I) mod (11+2I) = 5+4I", M3.powMod(E3, N3) == NeutrosophicInt(5, 4));
    }

    {
        NeutrosophicInt E(5, 6), phiN(12, 28), inv;
        bool ok = E.invMod(phiN, inv);
        check("A.7 invMod: (5+6I)^-1 mod (12+28I) = 5+6I", ok && inv == NeutrosophicInt(5, 6));

        NeutrosophicInt E2(17, 14), phiN2(72, 108), inv2;
        bool ok2 = E2.invMod(phiN2, inv2);
        check("A.7 invMod: (17+14I)^-1 mod (72+108I) = 17+134I", ok2 && inv2 == NeutrosophicInt(17, 134));

        NeutrosophicInt E3(2, 3), phiN3(9, 4), inv3;
        bool ok3 = E3.invMod(phiN3, inv3);
        check("A.7 invMod: (2+3I)^-1 mod (9+4I) = 5+3I", ok3 && inv3 == NeutrosophicInt(5, 3));

        NeutrosophicInt prod = E.mul(inv);
        mpz_class t1 = prod.a % phiN.a;
        mpz_class t2 = (prod.a + prod.b) % (phiN.a + phiN.b);
        check("A.7 invMod: (5+6I) times its inverse gives 1 in both coordinates", t1 == 1 && t2 == 1);

        NeutrosophicInt prod2 = E3.mul(inv3);
        mpz_class t3 = prod2.a % phiN3.a;
        mpz_class t4 = (prod2.a + prod2.b) % (phiN3.a + phiN3.b);
        check("A.7 invMod: (2+3I) times its inverse gives 1 in both coordinates", t3 == 1 && t4 == 1);
    }

    {
        NeutrosophicInt M(3, 3), E(5, 6), N(21, 34);
        NeutrosophicInt C = M.powMod(E, N);
        NeutrosophicInt phiN(12, 28), D;
        E.invMod(phiN, D);
        NeutrosophicInt back = C.powMod(D, N);
        check("RSA round-trip: decrypt(encrypt(3+3I)) = 3+3I", back == M);
    }
    cout << (failures == 0 ? "All Part A tests passed\n\n": "Some Part A tests failed\n\n");
}

// Part B

bool isPrime(const mpz_class &n) {
    return mpz_probab_prime_p(n.get_mpz_t(), 25) != 0;
}

mpz_class randomOdd(int bits) {
    mpz_class x = rng.get_z_bits(bits);
    mpz_setbit(x.get_mpz_t(), bits - 1);
    mpz_setbit(x.get_mpz_t(), 0);
    return x;
}

mpz_class generatePrime(int bits) {
    mpz_class x = randomOdd(bits);
    while (!isPrime(x)) x += 2;
    return x;
}

mpz_class generateSafePrime(int bits) {
    while (true) {
        mpz_class q = generatePrime(bits - 1);
        mpz_class p = 2 * q + 1;
        if (isPrime(p)) return p;
    }
}

NeutrosophicInt generateNeutroPrime(int bits, bool safe) {
    mpz_class first = safe ? generateSafePrime(bits) : generatePrime(bits);
    mpz_class sum;
    do {
        sum = safe ? generateSafePrime(bits) : generatePrime(bits);
    } while (sum == first);
    return NeutrosophicInt(first, sum - first);
}

mpz_class primitiveRoot(const mpz_class &p, const mpz_class &q) {
    mpz_class pm1 = p - 1;
    for (mpz_class g = 2; ; g++) {
        // Since p - 1 = 2q, the only possible orders are 1, 2, q and 2q.
        // These two tests rule out the smaller orders, leaving the full order 2q.
        if (powModPlain(g, pm1 / 2, p) != 1 && powModPlain(g, pm1 / q, p) != 1)
            return g;
    }
}

struct RSAKeys {
    NeutrosophicInt P, Q;
    NeutrosophicInt N;
    NeutrosophicInt E;
    NeutrosophicInt D;
};

RSAKeys rsaKeyGen(int bits) {
    RSAKeys k;

    k.P = generateNeutroPrime(bits, false);

    do {
        k.Q = generateNeutroPrime(bits, false);
    } while (!k.P.isCoprime(k.Q));

    k.N = k.P.mul(k.Q);
    NeutrosophicInt phiN = phiSFromPrimes(k.P, k.Q);
    k.E = NeutrosophicInt(65537, 0);
    if (!k.E.invMod(phiN, k.D)) return rsaKeyGen(bits);
    return k;
}

NeutrosophicInt rsaSign(const NeutrosophicInt &msg, const RSAKeys &k) {
    return msg.powMod(k.D, k.N);
}

bool rsaVerify(const NeutrosophicInt &msg, const NeutrosophicInt &sig, const NeutrosophicInt &E, const NeutrosophicInt &N) {
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

DHParams dhGenerateParams(int bits) {
    DHParams params;

    params.p1 = generateSafePrime(bits);
    params.q1 = (params.p1 - 1)/2;

    do {
        params.p2 = generateSafePrime(bits);
    } while (params.p2 == params.p1);
    params.q2 = (params.p2 - 1) / 2;

    params.P = NeutrosophicInt(params.p1, params.p2 - params.p1);

    mpz_class g1 = primitiveRoot(params.p1, params.q1);
    mpz_class g2 = primitiveRoot(params.p2, params.q2);
    params.G = NeutrosophicInt::fromCoords(g1, g2);
    return params;
}

bool hasFullGeneratorOrder(const mpz_class &g, const mpz_class &p, const mpz_class &q) {
    if (g <= 1 || g >= p) return false;

    return powModPlain(g, p - 1, p) == 1 && powModPlain(g, q, p) != 1 && powModPlain(g, 2, p) != 1;
}

bool areDhParametersValid(const DHParams &params) {
    mpz_class p1, p2, g1, g2;
    params.P.toCoords(p1, p2);
    params.G.toCoords(g1, g2);

    if (p1 != params.p1 || p2 != params.p2) return false;

    if (p1 <= 2 || p2 <= 2 || p1 == p2) return false;

    if (p1 != 2 * params.q1 + 1 || p2 != 2 * params.q2 + 1) return false;

    if (!isPrime(p1) || !isPrime(p2) || !isPrime(params.q1) || !isPrime(params.q2)) return false;

    if (mpz_sizeinbase(p1.get_mpz_t(), 2) < 256 || mpz_sizeinbase(p2.get_mpz_t(), 2) < 256) return false;

    return hasFullGeneratorOrder(g1, p1, params.q1) && hasFullGeneratorOrder(g2, p2, params.q2);
}

NeutrosophicInt randomSecret(int bits) {
    mpz_class e1 = rng.get_z_bits(bits) + 2;
    mpz_class e2 = rng.get_z_bits(bits);
    return NeutrosophicInt(e1, e2);
}

void partyProduceMessage(Party &who, const DHParams &params, int bits) {
    who.secret = randomSecret(bits);
    who.dhPublic = params.G.powMod(who.secret, params.P);
    who.signature = rsaSign(who.dhPublic, who.keys);
}

bool isValidDhPublicValue(const NeutrosophicInt &value, const DHParams &params) {
    mpz_class y1, y2;
    value.toCoords(y1, y2);

    // Exclude 0, 1 and p - 1 because they are not safe DH public values.
    return y1 > 1 && y1 < params.p1 - 1 && y2 > 1 && y2 < params.p2 - 1;
}

bool partyVerifyMessage(const Party &sender, const Message &m, const DHParams &params) {
    return isValidDhPublicValue(m.dhPublic, params) && rsaVerify(m.dhPublic, m.signature, sender.keys.E, sender.keys.N);
}


void partyDeriveSharedKey(Party &who, const NeutrosophicInt &peerPublic, const DHParams &params) {
    who.sharedKey = peerPublic.powMod(who.secret, params.P);
}

Message deliver(const Message &m, EveMode eve, const Party &eveParty, const Message &recorded, const DHParams &params, int bits, bool aliceToBob) {
    switch (eve) {
        case EVE_ABSENT:
            return m;

        case EVE_LAZY: {
            cout << "Eve replaces Alice's DH public value with her own but keeps Alice's signature\n";
            Party tmp = eveParty;
            tmp.secret = randomSecret(bits);
            tmp.dhPublic = params.G.powMod(tmp.secret, params.P);
            Message forged{tmp.dhPublic, m.signature};
            return forged;
        }

        case EVE_FORGE: {
            cout << "Eve replaces Alice's DH public value with her own and signs it with her own RSA key\n";
            Party tmp = eveParty;
            partyProduceMessage(tmp, params, bits);
            Message forged{tmp.dhPublic, tmp.signature};
            return forged;
        }

        case EVE_REPLAY:
            if (aliceToBob) {
                cout << "Eve replays the old DH public value and signature she recorded. The signature is genuine so this one passes the gate\n";
                return recorded;
            }
            return m;

        case EVE_TAMPER: {
            cout << "Eve passes along the message but flips one bit of Alice's DH public value first.\n";
            Message t = m;
            mpz_class flipped = t.dhPublic.a;
            mpz_setbit(flipped.get_mpz_t(), 0);
            if (flipped == t.dhPublic.a) mpz_clrbit(flipped.get_mpz_t(), 0);
            t.dhPublic.a = flipped;
            return t;
        }

        case EVE_IMPERSONATE_BOB:
            if (!aliceToBob) {
                cout << "Eve pretends to be Bob using her own DH public value signed with her own key\n";
                Party tmp = eveParty;
                partyProduceMessage(tmp, params, bits);
                Message forged{tmp.dhPublic, tmp.signature};
                return forged;
            }
            return m;

        case EVE_POISON_G:
            return m;
    }
    return m;
}

void runHandshake(const string &title, EveMode eve, Party &alice, Party &bob, Party &eveParty, DHParams params, int bits) {
    cout << "-----" << title << "-----" << "\n\n";

    if (eve == EVE_POISON_G) {
        cout << "Eve gets to the shared parameters first and then replaces the generator with 1 + 0I\n";
        params.G = NeutrosophicInt(1, 0);
    }

    if (!areDhParametersValid(params)) {
        cout << "The DH parameters are invalid therefore both sides reject the parameters and the protocol stops before exchange begins\n";
        return;
    }
    cout << "Parameter check passed because both modulus coordinates are safe primes and both generator coordinates have full order\n";

    Message recorded{};
    if (eve == EVE_REPLAY) {
        Party oldAlice = alice;
        partyProduceMessage(oldAlice, params, bits);
        recorded.dhPublic  = oldAlice.dhPublic;
        recorded.signature = oldAlice.signature;
        cout << "Before this run Eve managed to record one of Alice's old signed DH public values from an earlier session\n";
    }

    partyProduceMessage(alice, params, bits);
    cout << "\nStep 1: First Alice picks a fresh secret, computes her DH public value and then signs it with her RSA key\n";
    cout << " DH public value = " << alice.dhPublic << "\n";
    cout << " signature = " << alice.signature << "\n";

    Message wire1{alice.dhPublic, alice.signature};
    Message got1 = deliver(wire1, eve, eveParty, recorded, params, bits, true);

    cout << "\nStep 2: Bob checks the signature against Alice's long term public key (which he already trusts)\n";
    if (!partyVerifyMessage(alice, got1, params)) {
        cout << "The signature or DH public value is invalid so Bob stops here and no key is created\n\n";
        return;
    }
    cout << "It matches therefore this DH public value really is Alice's\n";

    partyProduceMessage(bob, params, bits);
    cout << "Bob answers with his own signed DH public value.\n";
    cout << " DH public value = " << bob.dhPublic << "\n";
    cout << " signature = " << bob.signature << "\n";

    Message wire2{bob.dhPublic, bob.signature};
    Message got2 = deliver(wire2, eve, eveParty, recorded, params, bits, false);

    cout << "\nStep 3: Alice checks Bob's signature the same way\n";
    if (!partyVerifyMessage(bob, got2, params)) {
        cout << " The signature or DH public value is invalid therefore Alice stops and no key is created\n\n";
        return;
    }
    cout << " It matches therefore the DH public value really is Bob's.\n";

    partyDeriveSharedKey(alice, got2.dhPublic, params);
    partyDeriveSharedKey(bob, got1.dhPublic, params);

    cout << "\nStep 4: Each side derives the shared key on their own\n";
    cout << " Alice gets " << alice.sharedKey << "\n";
    cout << " And Bob gets " << bob.sharedKey << "\n";

    if (alice.sharedKey == bob.sharedKey) {
        cout << "Both the keys are identical so agreement succeeded\n\n";
        return;
    }
    cout << "The keys differ.\n";
    if (eve == EVE_REPLAY) {
        cout << "Bob used Alice's old DH public value while Alice used Bob's new value. In this run, those two calculations produce different keys\n"
            "Eve still cannot calculate either key because she knows neither secret. However, the replay is accepted as authentic and disrupts the session because the messages have no freshness check\n\n";
    }
}

void partBDemos() {
    cout << "***** PART B (Authenticated DHKE) *****\n";
    cout << "Generating RSA key pairs for Alice, Bob, and Eve along with the shared DH group\n";

    const int RSA_BITS = 257;
    const int DH_BITS  = 256;

    Party alice, bob, eve;
    alice.name = "Alice";
    bob.name   = "Bob";
    eve.name   = "Eve";
    alice.keys = rsaKeyGen(RSA_BITS);
    bob.keys   = rsaKeyGen(RSA_BITS);
    eve.keys   = rsaKeyGen(RSA_BITS);

    DHParams params = dhGenerateParams(DH_BITS);

    mpz_class g1, g2;
    params.G.toCoords(g1, g2);
    cout << "DH public parameters:\n";
    cout << "P = " << params.P << "\n";
    cout << "Both coordinates of P are 256 bit safe primes p = 2q + 1\n\n";

    cout << "Finding a generator for the first coordinate p = " << params.p1.get_str() << ":\n";
    cout << " try g = " << g1.get_str() << "\n";
    cout << " g^((p-1)/2) mod p = " << powModPlain(g1, params.q1, params.p1).get_str() << "\n";
    cout << " g^((p-1)/q) mod p = " << powModPlain(g1, mpz_class(2), params.p1).get_str() << "\n";
    cout << " Neither result is 1, so " << g1.get_str() << " generates the units mod p.\n";
    cout << "By the same test the second coordinate accepts g = " << g2.get_str() << "\n\n";
    cout << "G = " << params.G << "\n";

    mpz_class coordOrder1 = params.p1 - 1, coordOrder2 = params.p2 - 1;
    mpz_class commonDivisor = ordinaryGcd(coordOrder1, coordOrder2);

    mpz_class ordG = coordOrder1 / commonDivisor * coordOrder2;
    cout << "ord(G) = lcm(a-1, a+b-1) = " << ordG << "\n\n";

    runHandshake("CASE 1: Clean handshake without Eve on the line", EVE_ABSENT, alice, bob, eve, params, DH_BITS);
    runHandshake("CASE 2: Eve swaps her own DH public value in but keeps Alice's signature", EVE_LAZY, alice, bob, eve, params, DH_BITS);
    runHandshake("CASE 3: Eve signs her own DH public value with her own key", EVE_FORGE, alice, bob, eve, params, DH_BITS);
    runHandshake("CASE 4: Eve replays an old signed DH public value from Alice", EVE_REPLAY, alice, bob, eve, params, DH_BITS);
    runHandshake("CASE 5: Eve flips one bit of Alice's DH public value", EVE_TAMPER, alice, bob, eve, params, DH_BITS);
    runHandshake("CASE 6: Eve answers Alice pretending to be Bob", EVE_IMPERSONATE_BOB, alice, bob, eve, params, DH_BITS);
    runHandshake("CASE 7: Eve replaces the shared generator with 1", EVE_POISON_G, alice, bob, eve, params, DH_BITS);
}

int main() {
    seedRng();
    partATests();
    partBDemos();
    return failures == 0 ? 0 : 1;
}
