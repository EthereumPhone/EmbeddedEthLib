# Hash-call and Keccak-f permutation counts for leanSPHINCS verify / keygen / sign, from the code structure.
# The structure is that of EthLib/Cryptography/Sphincs/*.lean and Merkle/Tree.lean, whose node and path recompute naively.
def perms(nbytes):
    return nbytes // 136 + 1


N, PRE = 16, 48
V, STEPS, TSUM = 64, 3, 128
c = {}  # name -> (calls, perms)


def add(d, k, calls, p):
    a = d.get(k, (0, 0))
    d[k] = (a[0] + calls, a[1] + p)


PRF = (1, perms(PRE + 32))  # Th over SK.seed: 80 B
F = (1, perms(PRE + N))  # chain step / FORS leaf: 64 B
H2 = (1, perms(PRE + 2 * N))  # tree node: 80 B
TV = (1, perms(PRE + V * N))  # T_v: 1072 B -> 8 perms
TK = (1, perms(PRE + 24 * N))  # T_k: 432 B -> 4 perms
ENC = (1, perms(PRE + N + 4))  # encode trial: 68 B
HMSG = (2, 2 * perms(84))


def mul(t, k):
    return (t[0] * k, t[1] * k)


def plus(*ts):
    return (sum(t[0] for t in ts), sum(t[1] for t in ts))


OTS_LEAF = plus(mul(PRF, V), mul(F, V * STEPS), TV)  # otsPublicLeaf


def tree_root(h):
    return plus(mul(OTS_LEAF, 2**h), mul(H2, 2**h - 1))


def tree_path(h):  # sum over z<h of node(z): 2^z leaves + 2^z - 1 nodes
    return plus(*[plus(mul(OTS_LEAF, 2**z), mul(H2, 2**z - 1)) for z in range(h)])


FORS_LEAF = plus(PRF, F)


def fors_node(z):
    return plus(mul(FORS_LEAF, 2**z), mul(H2, 2**z - 1))


FORS_ROOT = fors_node(10)
FORS_OPEN = plus(PRF, *[fors_node(z) for z in range(10)])
EXPAND = (2, 2 * perms(11 + 32 + 1))
PRFMSG = (1, perms(32 + 16 + 45))
verify = plus(
    HMSG, mul(plus(F, mul(H2, 10)), 24), TK, mul(plus(ENC, mul(F, 64), TV), 3), mul(H2, 26)
)
keygen = plus(EXPAND, tree_root(10))


def ots_sign(trials):
    return plus(mul(ENC, trials), mul(PRF, V), mul(F, TSUM))


def sign(trials):
    return plus(
        EXPAND,
        tree_root(10),
        PRFMSG,
        HMSG,
        mul(FORS_OPEN, 24),  # forsSign
        mul(FORS_ROOT, 24),
        TK,  # bottom layerMessage = forsKey
        ots_sign(trials[0]),
        tree_path(8),  # bottom signLayer
        tree_root(8),  # middle layerMessage (bottom tree root)
        ots_sign(trials[1]),
        tree_path(8),
        tree_root(8),  # top layerMessage (middle tree root)
        ots_sign(trials[2]),
        tree_path(10),
    )


kat = [6980 + 1, 6954 + 1, 736 + 1]  # counters in the KAT signature, +1 (search starts at 0)
for name, t in [
    ("verify", verify),
    ("keygen", keygen),
    ("sign_KAT", sign(kat)),
    ("sign_avg(3x14670 trials)", sign([14670] * 3)),
    ("ots_leaf", OTS_LEAF),
    ("fors_leaf", FORS_LEAF),
]:
    print(f"{name:28s} calls={t[0]:>9,d} perms={t[1]:>9,d}")
