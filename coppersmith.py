import shutil
import subprocess
import re

from sage.misc.converting_dict import KeyConvertingDict
from sage.all import matrix, ZZ, DiGraph, Infinity, prod, Sequence, PolynomialRing, TermOrder, QQ

from warnings import warn
from collections import defaultdict
from subprocess import CalledProcessError

import logging

logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO, format='%(uptime)f [%(levelname)s]: %(message)s')

old_factory = logging.getLogRecordFactory()
def record_factory(*args, **kwargs):
    record = old_factory(*args, **kwargs)
    record.uptime = record.relativeCreated/1000
    return record
logging.setLogRecordFactory(record_factory)


flatter_path = shutil.which('flatter')

# test if msolve is installed
try:
    QQ['x,y'].ideal([1]).groebner_basis(algorithm='msolve', proof=False)
    msolve_available = True
except CalledProcessError:
    warn('msolve not found by Sage, equation solving will likely be slower')
    msolve_available = False


def flatter(M, flatter_path=flatter_path):
    inp_str = '[' + '\n'.join('[' + ' '.join(map(str, row)) + ']' for row in M) + ']'
    out_str = subprocess.check_output([flatter_path], input=inp_str.encode())
    return matrix(ZZ, M.nrows(), M.ncols(), map(ZZ, re.findall(r'-?\d+', out_str.decode())))


def groebner_ZZ(I):
    # TODO: add magma support
    return I.groebner_basis()


def groebner_QQ(I):
    '''
    Return a new ideal with either the Gröbner basis of I
    as generators or return I with a cached computed Gröbner basis
    '''
    if msolve_available:
        gb = I.groebner_basis(algorithm='msolve', proof=False)
    else:
        gb = I.groebner_basis()
    return I.parent()(gb)


def variety_QQ(I):
    '''
    Return the variety of I
    '''
    if msolve_available:
        return I.variety(algorithm='msolve', proof=False)
    return I.variety()


def LLL(M, **kwargs):
    return M.LLL(**kwargs)


def BKZ(M, **kwargs):
    return M.BKZ(**kwargs)


def lg2(n):
    return ZZ(abs(n) - 1).nbits()


def optimal_shift_polys(G, M):
    S = []
    for m in M:
        g = min((g for g in G if g.lm().divides(m)), key=lambda g: g.lc(), default=None)
        if g is None:
            raise ValueError('ideal behaves unexpectedly, please report this')
        h = g * (m // g.lm())
        hprim = h.lt() + (h - h.lt()).reduce(G)
        S.append(hprim)
    return S


def suitable_subset(MS, var_sizes):
    G = DiGraph(len(MS) + 2, weighted=True)

    mono_weight = lambda m: sum(a*b for a, b in zip(m.exponents()[0], var_sizes))
    poly_weight = lambda t: lg2(t.lc()) + mono_weight(t.lm())

    S = [s for _, s in MS]
    M_idx = {m: i for i, (m, _) in enumerate(MS)}
    nmonos = len(MS)

    off = sum(map(poly_weight, S)) / len(S)
    vert_weights = [off - poly_weight(g) for g in S]

    # Reduce maximum-closure to maximum-cut like described in
    # https://en.wikipedia.org/wiki/Closure_problem#Reduction_to_maximum_flow
    for f in S:
        m1 = f.lm()
        i1 = M_idx[m1]
        wm = vert_weights[i1]
        if wm > 0:
            G.add_edge(nmonos, i1, wm)
        else:
            G.add_edge(i1, nmonos+1, -wm)

        for m2 in f.monomials():
            if m1 == m2:
                continue
            i2 = M_idx[m2]
            G.add_edge(i1, i2, Infinity)
    
    parts = G.edge_cut(nmonos, nmonos+1, value_only=False, use_edge_labels=True, vertices=True)[2]
    closure = set(next(c for c in parts if nmonos in c))
    closure -= {nmonos, nmonos+1}

    if sum(vert_weights[i] for i in closure) == 0:
        return None
    return [MS[i] for i in closure]


def find_exps(assignemnt, remaining, weights):
    i = len(assignemnt)
    if i == len(weights):
        yield assignemnt
        return

    weight = weights[i]
    for j in range(remaining + 1):
        new_remaining = remaining - j * weight
        if new_remaining < 0:
            break
        yield from find_exps(assignemnt + (j,), new_remaining, weights)


def small_roots(inp_polys, sizes, ks=None, mod_bounds=None, lat_reduce=flatter, graph_search=True):
    '''
    Given a list of polynomials, possible over different rings, finds
    small solutions to the system of equations. The polynomials may be defined
    over ZZ, QQ or Zmod(N) (even for different N).

    Matching of variables across different rings is done by name (as strings).

    Args:
        inp_polys: list of polynomials
        sizes: dict mapping variable names to their sizes (in no. bits)
        ks: dict mapping moduli to exponent multiplicity in the ideal (1 if
            not present)
        mod_bounds: dict mapping moduli to bound on the divisor we want roots
            modulo (in no. bits)
        lat_reduce: function to reduce the lattice, defaults to flatter if
            installed otherwise fplll's LLL
        greap_search: Whether to perform the graph search to find dense sublattices

    Returns:
        list of solutions, each a dict mapping variable names to their values
    '''
    if ks is None:
        ks = {}
    if mod_bounds is None:
        mod_bounds = {}
    sizes = {str(n): b for n, b in sizes.items()}

    var_names = set()
    for inp_poly in inp_polys:
        var_names |= {str(x) for x in inp_poly.variables()}
    var_names = tuple(sorted(var_names))
    try:
        var_sizes = [ZZ(sizes[n]) for n in var_names]
    except KeyError as e:
        raise ValueError(f"Variable {e} not found in bounds")

    polyring, xs = PolynomialRing(
        ZZ, len(var_names), var_names, order=TermOrder("wdeglex", var_sizes)
    ).objgens()

    char_to_polys = defaultdict(list)
    for inp_poly in inp_polys:
        R = inp_poly.base_ring()
        if R == QQ:
            inp_poly *= inp_poly.denominator()
        char_to_polys[R.characteristic()].append(polyring(repr(inp_poly)))
    logger.info("computing ideal powers...")

    # TODO: smarter selection of powers
    Jps = []
    mod_sz = 0
    for char, polys in char_to_polys.items():
        if char == 0:
            continue
        k = ks.pop(char, 1)
        Jps.append(polyring.ideal(polys + [char]) ** k)
        mod_sz += mod_bounds.get(char, lg2(char)) * k
    J = char_to_polys.get(0, [])
    if Jps: J += prod(Jps)
    logger.info(f"{len(J.gens())} generators in ideal, computing Gröbner basis...")

    # TODO: better gröbner libraries?

    if ks:
        raise ValueError(f"Unused moduli: {list(ks.keys())}")

    Mbig = [
        prod(x**i for x, i in zip(xs, exp))
        for exp in find_exps((), mod_sz, var_sizes)
    ]

    G = groebner_ZZ(J)
    MSbig = [(m, s) for m, s in zip (Mbig, optimal_shift_polys(G, Mbig))]

    MSheur = MSbig

    if graph_search:
        pre_sz = len(MSheur)
        logger.info(f"finding suitable subset using graph search...")
        while (cand := suitable_subset(MSheur, var_sizes)) is not None:
            MSheur = cand
        logger.info(f'went from {pre_sz} -> {len(MSheur)} monomials')

    Ssub = [s for _, s in MSheur]

    L, monos = Sequence(Ssub).coefficients_monomials()
    mono_weights = [
        sum(a * b for a, b in zip(mono.exponents()[0], var_sizes)) for mono in monos
    ]

    for i, w in enumerate(mono_weights):
        L.rescale_col(i, 2**w)

    if lat_reduce is None:
        if flatter_path is None:
            warn('flatter not found, lattice reduction will be slower')
            lat_reduce = LLL
        else:
            lat_reduce = flatter

    if L.nrows() < 2:
        raise ValueError('lattice got too small, try disabling graph search')

    logger.info(f"reducing {L.nrows()}x{L.ncols()} matrix...")
    L = lat_reduce(L.dense_matrix())

    try:
        poly_end_idx = max(i+1 for i, r in enumerate(L) if r.norm(1) < 2**mod_sz)
    except ValueError:
        poly_end_idx = 1

    L = L.change_ring(QQ)
    for i, w in enumerate(mono_weights):
        L.rescale_col(i, QQ(2) ** -w)

    out_polys = list(L * monos)
    out_polys = [f if not f.is_constant() else f.parent()(0) for f in out_polys]
    while 0 < poly_end_idx <= len(out_polys):
        sol_polys = out_polys[:poly_end_idx]
        logger.info(f'solving with the first {poly_end_idx} polynomials...')
        part_var_names = list(
            set().union(*({str(x) for x in p.variables()} for p in sol_polys))
        )
        part_ring = PolynomialRing(
            QQ, len(part_var_names), part_var_names, order="degrevlex"
        )
        I = part_ring.ideal([part_ring(repr(p)) for p in sol_polys])
        I = groebner_QQ(I)
        if I.dimension() == 0: break
        if I.dimension() == -1: poly_end_idx -= 1
        if I.dimension() > 0: poly_end_idx += 1
    else:
        return []

    rem_var_names = set(var_names) - set(part_var_names)
    if len(rem_var_names) > 0:
        warn(
            f"Variables {rem_var_names} not recovered, "
            "try substituting the result back into the original equations"
        )

    logger.info('0-dimensional ideal found, computing variety...')

    # TODO: try to solve for all variables even if left out
    # in the final equations (combine with initial equations?)
    return [
        KeyConvertingDict(str, {str(k): ZZ(v) for k, v in sol.items()})
        for sol in variety_QQ(I) if all(sol.is_integer() for sol in sol.values())
    ]