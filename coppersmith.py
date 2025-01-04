import shutil
import subprocess
import re
import logging

from sage.misc.converting_dict import KeyConvertingDict
from sage.all import matrix, ZZ, DiGraph, Infinity, prod, Sequence, PolynomialRing, TermOrder, QQ

from functools import lru_cache
from collections import defaultdict
from subprocess import CalledProcessError


logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO, format='%(uptime)f [%(levelname)s]: %(message)s')

old_factory = logging.getLogRecordFactory()
def record_factory(*args, **kwargs):
    record = old_factory(*args, **kwargs)
    record.uptime = record.relativeCreated/1000
    return record
logging.setLogRecordFactory(record_factory)

@lru_cache(None)
def warn_once(logger, msg):
    logger.warning(msg)


flatter_path = shutil.which('flatter')

# test if msolve is installed
try:
    QQ['x,y'].ideal([1]).groebner_basis(algorithm='msolve', proof=False)
    msolve_available = True
except CalledProcessError:
    logger.warning('msolve not found by Sage, equation solving will likely be slower')
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
    as generators
    '''
    if msolve_available:
        gb = I.groebner_basis(algorithm='msolve', proof=False)
    else:
        gb = I.groebner_basis()
    return I.parent()(gb)


def variety_ZZ(I):
    '''
    Return the variety of I
    '''
    if msolve_available:
        vari = I.variety(algorithm='msolve', proof=False)
    else:
        vari = I.variety()
    return [
        KeyConvertingDict(str, {str(k): ZZ(v) for k, v in sol.items()})
        for sol in vari if all(sol.is_integer() for sol in sol.values())
    ]


def LLL(M, **kwargs):
    return M.LLL(**kwargs)


def BKZ(M, **kwargs):
    return M.BKZ(**kwargs)


def lg2(n):
    return ZZ(abs(n) - 1).nbits()


def common_ZZ_ring(polys):
    var_names = set().union(*({str(x) for x in p.variables()} for p in polys))
    return PolynomialRing(ZZ, len(var_names), tuple(var_names))


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


def suitable_subset(MS, X):
    G = DiGraph(len(MS) + 2, weighted=True)

    S = [s for _, s in MS]
    M_idx = {m: i for i, (m, _) in enumerate(MS)}
    nmonos = len(MS)

    poly_weights = [ZZ(lg2(f.lt()(X))) for f in S]
    off = sum(poly_weights) / len(S)
    vert_weights = [off - w for w in poly_weights]

    # Reduce maximum-closure to minimum-cut like described in
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


def small_polys(inp_polys, sizes, ks=None, mod_bounds=None, lat_reduce=flatter, graph_search=True, ret_start_hint=False):
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
        graph_search: Whether to perform the graph search to find dense sublattices
        ret_start_hint: Whether to also return the index at which the resulting polynomials
            get larger than the modulus

    Returns:
        list of solutions, each a dict mapping variable names to their values
    '''
    if ks is None:
        ks = {}
    if mod_bounds is None:
        mod_bounds = {}
    sizes = {str(n): b for n, b in sizes.items()}
    
    polyring = common_ZZ_ring(inp_polys)

    try:
        var_sizes = [ZZ(sizes[n]) for n in polyring._names]
    except KeyError as e:
        raise ValueError(f"Variable {e} not found in bounds")
    
    polyring = polyring.change_ring(order=TermOrder("wdeglex", var_sizes))

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
    J_inf = polyring.ideal(char_to_polys.get(0, []))
    J = J_inf
    if Jps: J += prod(Jps)
    logger.info(f"{len(J.gens())} generators in ideal, computing Gröbner basis...")


    if ks:
        raise ValueError(f"Unused moduli: {list(ks.keys())}")

    Mbig = [
        prod(x**i for x, i in zip(polyring.gens(), exp))
        for exp in find_exps((), mod_sz, var_sizes)
    ]

    # J_inf_lm = polyring.ideal([f.lm() for f in J_inf.groebner_basis()])
    # Mbig = [m for m in Mbig if m not in J_inf_lm]

    G = groebner_ZZ(J)
    MSheur = [(m, s) for m, s in zip (Mbig, optimal_shift_polys(G, Mbig))]

    X = [2**sz for sz in var_sizes]

    if graph_search:
        pre_sz = len(MSheur)
        logger.info(f"finding suitable subset using graph search...")
        while (cand := suitable_subset(MSheur, X)) is not None:
            MSheur = cand
        logger.info(f'went from {pre_sz} -> {len(MSheur)} monomials')

    Ssub = [s for _, s in MSheur]

    L, monos = Sequence(Ssub).coefficients_monomials()

    for i, mono in enumerate(monos):
        L.rescale_col(i, mono(X))

    if lat_reduce is None:
        if flatter_path is None:
            warn_once('flatter not found, lattice reduction will be slower')
            lat_reduce = LLL
        else:
            lat_reduce = flatter

    if L.nrows() < 3:
        raise ValueError('lattice got too small, try disabling graph search')

    logger.info(f"reducing {L.nrows()}x{L.ncols()} matrix...")
    L = lat_reduce(L.dense_matrix())

    start_hint = next((i for i, r in enumerate(L) if r.norm(1) > 2**mod_sz), len(monos))

    L = L.change_ring(QQ)
    for i, mono in enumerate(monos):
        L.rescale_col(i, QQ((1, mono(X))))

    res = list(L.change_ring(ZZ) * monos)
    if ret_start_hint:
        return res, start_hint
    return res


def small_roots(inp_polys, sizes, ks=None, mod_bounds=None, lat_reduce=flatter, graph_search=True, algorithm='groebner'):
    '''
    See docstring of `small_polys`
    '''
    out_polys, start_hint = small_polys(inp_polys, sizes, ks, mod_bounds, lat_reduce, graph_search, ret_start_hint=True)
    logger.info('found small polys, solving for roots...')

    if algorithm == 'groebner':
        return rootfind_groebner(out_polys, start_hint=start_hint)
    else:
        raise ValueError(f"Unknown algorithm {algorithm}")

# TODO: add more rootfinding algorithms

def rootfind_groebner(polys, start_hint=None):
    seen_params = set()

    if start_hint is not None:
        idx = start_hint
        while 0 < idx <= len(polys):
            logger.info(f'trying Gröbner with {idx} first polynomials...')
            params = tuple(range(idx))
            if params in seen_params:
                # looped back to a previous state
                break

            seen_params.add(params)

            part_ring = common_ZZ_ring(polys[:idx]).change_ring(QQ, order='degrevlex')
            I = part_ring.ideal([part_ring(repr(p)) for p in polys[:idx]])
            I = groebner_QQ(I)

            if I.dimension() == 0:
                return variety_ZZ(I)
            if I.dimension() == -1: idx -= 1
            if I.dimension() > 0: idx += 1

    logger.info(f'successively adding more polynomials from start...')
    sol_polys = []
    param = ()
    for i, p in enumerate(polys):
        param += (i,)
        # don't repeat something the previous loop above did
        if param in seen_params: continue

        sol_polys.append(p)
        part_ring = common_ZZ_ring(sol_polys).change_ring(QQ, order='degrevlex')
        I = part_ring.ideal([part_ring(repr(p)) for p in sol_polys])
        I = groebner_QQ(I)

        if I.dimension() == 0:
            return variety_ZZ(I)
        if I.dimension() == -1:
            param = param[:-1]
            sol_polys.pop()
    return []