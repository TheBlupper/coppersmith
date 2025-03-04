# Coppersmith

### The author has now released [their own implementation](https://github.com/keeganryan/cuso) which is a lot better in every way, I'm just keeping this repo for historical purposes

A toy partial implementation of [Solving Multivariate Coppersmith Problems with Known Moduli](https://eprint.iacr.org/2024/1577.pdf), which generalizes the finding of small roots of polynomials modulo integers.

It makes use of Gröbner bases to find optimal* shift polynomials for systems of polynomial equations, possibly with different moduli. The current state of the code is highly non-optimized and any contributions are welcome. See [examples.py](./examples.py) for usage.

None of the symbolic precomputation in the paper is currently implemented.

\* "Optimal" is defined in the paper
