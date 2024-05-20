

from math import log2, ceil
def cl2(v: int, min1=True) -> int:
    return int(ceil(log2(v))) if (v > 1 or not min1) else 1

from typing import Callable, TypeVar, Iterable, Any
_T = TypeVar('_T')
def tree_reduce(func: Callable[[_T, _T], _T], data: Iterable[_T]) -> _T:
    N = len(data)
    assert N > 0, "Can't reduce an empty Iterable"
    if N == 1:
        return data[0]
    N0 = N//2

    return func(tree_reduce(func, data[:N0]), tree_reduce(func, data[N0:]))

def max_tree(m, A, reg_dist=3):

    def max_f(a, b):
            nonlocal m
            nonlocal reg_dist
            a, ac = a
            b, bc = b

            max_v = Signal(max(len(a), len(b)))
            muxeq = max_v.eq(Mux(a > b, a, b))
            d = max(ac, bc)
            if d == reg_dist:
                m.d.sync += muxeq
                return max_v, 0
            else:
                m.d.comb += muxeq
                return max_v, d+1
    
    maxret, _ = tree_reduce(max_f, list(zip(A, [0]*len(A))))
    return maxret

def sliceSize(s: slice, baseWidth: int) -> int:
    start, end, stride = s.indices(baseWidth)
    return (end-start) // stride

from amaranth.lib.data import *
def getSlice(f: Field) -> slice:
    return slice(f.offset, f.offset+f.width)


def accessField(L: Layout, *key: Any) -> Field:
    l = L
    for k in key:
        f = l[k]
        l = f.shape
    return f


def ifGen(m, S, withElse=False, startFromIf=True):
    S = iter(S)
    if startFromIf:
        yield m.If(next(S))
    for s in S:
        yield m.Elif(s)
    if withElse:
        yield m.Else()

def equalByName(A, B, layoutA=None, omit=[]):

    if layoutA==None and hasattr(A, "shape"):
        layoutA = A.shape()

    if not isinstance(layoutA, Layout):
        yield A.eq(B)
        return

    for name, field in layoutA._fields.items():
        if name in omit:
            continue
        if isinstance(field.shape, StructLayout):
            yield from equalByName(A[name], B[name], field.shape, omit)
        elif isinstance(field.shape, ArrayLayout):
            for n in range(field.shape.length):
                yield from equalByName(A[name][n], B[name][n], field.shape.elem_shape, omit)
        elif isinstance(field.shape, UnionLayout):
            first = list(field.shape._fields.keys())[0]
            yield from equalByName(A[name][first], B[name][first], field.shape[first].shape, omit)
        else:
            yield A[name].eq(B[name])


def constMult(x, c):
    lc = cl2(c+1)
    
    cBits = [(c & (1 << i)) != 0 for i in range(lc)]
    nc = (~c)+1
    ncBits = [(nc & (1 << i)) != 0 for i in range(lc)]
    neg = (sum(ncBits)+1) < sum(cBits)

    if neg:
        cBits = ncBits
    
    shift = lambda v, a: (v << a) if a != 0 else v
    S = []
    for i, b in enumerate(cBits):
        if b:
            S.append(shift(x, i))
    
    s = tree_reduce(lambda a, b: a+b, S)
    if neg:
        return shift(x,lc) - s
    else:
        return s    


def filter_dict(remove, d):
    return dict(filter(lambda p: p[0] not in remove, d.items()))

from amaranth import *
#RoundRobin. Deprecated in amaranth.lib
class RoundRobin(Elaboratable):
    """Round-robin scheduler.

    For a given set of requests, the round-robin scheduler will
    grant one request. Once it grants a request, if any other
    requests are active, it grants the next active request with
    a greater number, restarting from zero once it reaches the
    highest one.

    Use :class:`EnableInserter` to control when the scheduler
    is updated.

    Parameters
    ----------
    count : int
        Number of requests.

    Attributes
    ----------
    requests : Signal(count), in
        Set of requests.
    grant : Signal(range(count)), out
        Number of the granted request. Does not change if there are no
        active requests.
    valid : Signal(), out
        Asserted if grant corresponds to an active request. Deasserted
        otherwise, i.e. if no requests are active.
    """
    def __init__(self, *, count):
        if not isinstance(count, int) or count < 0:
            raise ValueError("Count must be a non-negative integer, not {!r}"
                             .format(count))
        self.count    = count

        self.requests = Signal(count)
        self.grant    = Signal(range(count))
        self.valid    = Signal()

    def elaborate(self, platform):
        m = Module()

        with m.Switch(self.grant):
            for i in range(self.count):
                with m.Case(i):
                    for pred in reversed(range(i)):
                        with m.If(self.requests[pred]):
                            m.d.sync += self.grant.eq(pred)
                    for succ in reversed(range(i + 1, self.count)):
                        with m.If(self.requests[succ]):
                            m.d.sync += self.grant.eq(succ)

        m.d.sync += self.valid.eq(self.requests.any())

        return m
