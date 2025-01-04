from sage.all import *
from coppersmith import small_roots


def test_mihnp(nsamples, lgX, lgp, k):
    print(f'testing MIHNP with nsamples={nsamples}, lgX={lgX}, lgp={lgp}, k={k}')

    p = random_prime(2**lgp)
    f, *xs = polygens(GF(p), ['f'] + [f'k{i}' for i in range(nsamples)])

    A = ZZ(randrange(p))
    tgt = [pow(A+i, -1, p) >> lgX for i in range(nsamples)]

    polys = [(f+i)*((h<<lgX)+x)-1 for i, (h, x) in enumerate(zip(tgt, xs))]

    # we don't get f back since it is eliminated early because of its size
    # this is a bit annoying to deal with, an option is solve over ZZ then add
    # this back to the original equations. this is a bit hard to generlise though
    # lmk if you come up with a good solution
    sol = small_roots(polys, {f: A.nbits()+1} | {x: lgX+1 for x in xs}, {p: k})[0]

    a = pow((tgt[0]<<lgX) + sol[xs[0]], -1, p)
    assert A == a


def test_system_univariate(lgX, lgp, e1, e2, k1, k2):
    print(f'testing univariate system with lgX={lgX}, lgp={lgp}, e1={e1}, e2={e2}, k1={k1}, k2={k2}')

    N1 = random_prime(2**lgp) * random_prime(2**lgp)
    N2 = random_prime(2**lgp) * random_prime(2**lgp)
    a1, b1 = randrange(N1), randrange(N1)
    a2, b2 = randrange(N2), randrange(N2)

    x = polygen(ZZ, 'x')
    xn1, xn2 = x.change_ring(Zmod(N1)), x.change_ring(Zmod(N2))

    m = randrange(2**lgX)
    c1, c2 = pow(a1*m+b1, e1, N1), pow(a2*m+b2, e2, N2)

    f1 = (a1*xn1 + b1)**e1 - c1
    f2 = (a2*xn2 + b2)**e2 - c2
    assert small_roots([f1, f2], {x: lgX}, {N1: k1, N2: k2})[0][x] == m


def test_partial_factor(lgp, lgX, k):
    print(f'testing partial factorization with lgX={lgX}, lgp={lgp}, k={k}')
    p = random_prime(2**lgp)
    q = random_prime(2**lgp)
    N = p*q
    x = polygen(Zmod(N), 'x')

    a = (p>>lgX)<<lgX
    assert small_roots([x+a], {x: lgX}, {N: k}, {N: lgp})[0][x] + a == p


def run_tests():
    # these are slightly probabilistic so they fail sporadically
    # at least they work for this seed
    set_random_seed(0)

    test_partial_factor(lgp=1024, lgX=330, k=1)
    test_partial_factor(lgp=1024, lgX=460, k=5)
    test_partial_factor(lgp=1024, lgX=490, k=15)

    test_system_univariate(lgX=291, lgp=512, e1=3, e2=5, k1=1, k2=1)
    test_system_univariate(lgX=365, lgp=512, e1=3, e2=5, k1=2, k2=2)
    test_system_univariate(lgX=455, lgp=512, e1=3, e2=5, k1=5, k2=4)

    test_mihnp(nsamples=4, lgX=370, lgp=1000, k=1)
    test_mihnp(nsamples=4, lgX=405, lgp=1000, k=2)
    test_mihnp(nsamples=5, lgX=470, lgp=1000, k=3)


if __name__ == '__main__':
    run_tests()