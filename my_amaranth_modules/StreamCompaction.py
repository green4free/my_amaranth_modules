
from Stream import BasicStreamInterface, StreamReg
from amaranth import *
from typing import Hashable
from amaranth.lib.data import *
from utils import cl2
from Algorithms import perfectSortings
class CompactionIndexesDeprecated(Elaboratable):

    def __init__(self, N=4, dir=0, passNV=False):
        self.N = N
        self.passNV = passNV
        self.dir = dir
        self.valid_i = Signal(N)
        self.valid_o = Signal(N)
        self.indexes = Signal(ArrayLayout(unsigned(cl2(N)), N))

    def elaborate(self, platform):

        m = Module()
        if m.setPureIdentifier(type(self),self.N, self.passNV, self.dir):
            m.submodules += Instance("dummy", i_valid_i=self.valid_i, o_valid_o=self.valid_o, o_indexes=self.indexes)
            return m

        print("Elaborating ", self.__class__.__name__, self)

        def T(si, so):
            with m.If(si[0][0]):
                m.d.comb += so[0].eq(si[0])
                if len(si)>1:
                    T(si[1:], so[1:])
            with m.Else():
                if self.passNV:
                    m.d.comb += so[-1].eq(si[0])
                else:
                    m.d.comb += so[-1].eq(0)
                if len(si)>1:
                    T(si[1:], so[:-1])
        W = len(self.indexes[0])

        D = range(self.N)
        if self.dir:
            D = reversed(D)

        T(
            [Cat(self.valid_i[i], Const(i, W)) for i in range(self.N)],
            [Cat(self.valid_o[i], self.indexes[i]) for i in D]
        )
        return m



class CompactionIndexes(Elaboratable):

    def __init__(self, N=4, dir=0, passNV=False, index_in=False, stable=False, width=None, registers=[], optimized_valid_in=False, optimized_valid_out=False):
        self.N = N
        self.passNV = passNV
        self.dir = dir
        self.index_in = index_in
        self.valid_i = Signal(N)
        self.valid_o = Signal(N)
        self.width = width if width != None else cl2(N)
        self.indexes = Array(Signal(self.width, name=f"index{i}") for i in range(self.N))
        self.stable = stable
        self.registers = registers
        self.optimized_valid_in = optimized_valid_in and len(registers) > 0
        self.optimized_valid_out = optimized_valid_out and len(registers) > 0
        if self.optimized_valid_in:
            self.o_valid_in = Signal()
        if self.optimized_valid_out:
            self.o_valid_out = Signal()
        if len(registers) > 0:
            self.ready_i = Signal()
            self.ready_o = Signal()
        
        if index_in:
            self.indexes_in = Array(Signal(self.width, name=f"index_in{i}") for i in range(self.N))
        else:
            self.indexes_in = Array(Const(i, self.width) for i in range(self.N))

    def elaborate(self, platform):

        m = Module()
        if m.setPureIdentifier(type(self),self.N, self.passNV, self.dir, self.index_in, self.width, self.stable, tuple(self.registers), self.optimized_valid_in, self.optimized_valid_out):
            ii = {"i_indexes_in":self.indexes_in} if self.index_in else {}
            syncs = {"i_clk":ClockSignal("sync"), "i_rst":ResetSignal("sync")} if len(self.registers) > 0 else {}
            readys = {"i_ready_i":self.ready_i, "o_ready_o":self.ready_o} if len(self.registers) > 0 else {}
            ovi = {"i_o_valid_in":self.o_valid_in} if self.optimized_valid_in else {}
            ovo = {"o_o_valid_out":self.o_valid_out} if self.optimized_valid_out else {}
            m.submodules += Instance("dummy", i_valid_i=self.valid_i, o_valid_o=self.valid_o, o_indexes=self.indexes, **ii, **syncs, **readys, **ovi, **ovo)
            return m

        print("Elaborating ", self.__class__.__name__, self)
        
        regLayers = {}
        W = (cl2(self.N)+self.width) if self.stable and self.index_in else self.width

        def swap2(U, V, d):
            Vu, Eu = U
            Vv, Ev = V
            
            if not self.passNV:
                Eu = Vu.replicate(W) & Eu
                Ev = Vv.replicate(W) & Ev

            B = ((Signal(), Signal(W)), (Signal(), Signal(W)))
            if d:
                if self.stable:
                    indexComp = Signal()
                    m.d.comb += indexComp.eq(Eu[self.width:] > Ev[self.width:])
                    with m.If(Vu & Vv):
                        m.d.comb += [B[1][0].eq(1), B[1][1].eq(Mux(indexComp, Eu, Ev)), B[0][0].eq(1), B[0][1].eq(Mux(indexComp, Ev, Eu))]
                    with m.Elif(Vu):
                        m.d.comb += [B[1][0].eq(1), B[1][1].eq(Eu), B[0][0].eq(Vv), B[0][1].eq(Ev)]
                else:
                    with m.If(Vu):
                        m.d.comb += [B[1][0].eq(1), B[1][1].eq(Eu), B[0][0].eq(Vv), B[0][1].eq(Ev)]
                    
                with m.Elif(Vv):
                    m.d.comb += [B[1][0].eq(1), B[1][1].eq(Ev), B[0][0].eq(Vu), B[0][1].eq(Eu)]
                with m.Else():
                    m.d.comb += [B[1][0].eq(0), B[1][1].eq(Eu), B[0][0].eq(0), B[0][1].eq(Ev)]
            else:
                if self.stable:
                    indexComp = Signal()
                    m.d.comb += indexComp.eq(Eu[self.width:] < Ev[self.width:])
                    with m.If(Vu & Vv):
                        m.d.comb += [B[0][0].eq(1), B[0][1].eq(Mux(indexComp, Eu, Ev)), B[1][0].eq(1), B[1][1].eq(Mux(indexComp, Ev, Eu))]
                    with m.Elif(Vu):
                        m.d.comb += [B[0][0].eq(1), B[0][1].eq(Eu), B[1][0].eq(Vv), B[1][1].eq(Ev)]
                else:
                    with m.If(Vu):
                        m.d.comb += [B[0][0].eq(1), B[0][1].eq(Eu), B[1][0].eq(Vv), B[1][1].eq(Ev)]
                
                with m.Elif(Vv):
                    m.d.comb += [B[0][0].eq(1), B[0][1].eq(Ev), B[1][0].eq(Vu), B[1][1].eq(Eu)]
                with m.Else():
                    m.d.comb += [B[0][0].eq(0), B[0][1].eq(Eu), B[1][0].eq(0), B[1][1].eq(Ev)]
            return B
        
        def bSort(A, d, l=0):
            cnt = len(A)
            if cnt <= 1:
                return A, l
            elif cnt in perfectSortings.keys():
                sorter = perfectSortings[cnt]
                for layer in sorter:
                    for swap in layer:
                        i0, i1 = swap
                        A[i0], A[i1] = swap2(A[i0], A[i1], d)
                    l += 1
                    if l in self.registers:
                        B = [(Signal(), Signal(W)) for _ in range(len(A))]
                        s = regLayers.get(l,None)
                        v_b, e_b = zip(*B)
                        v_a, e_a = zip(*A)

                        if s == None:
                            regLayers[l] = e_a, v_a, e_b, v_b
                        else:
                            aE, aV, bE, bV = s
                            regLayers[l] = aE+e_a, aV+v_a, bE+e_b, bV+v_b
                        A = B
                return A, l
            else:
                k = cnt//2
                B = [(Signal(), Signal(W)) for _ in range(len(A))]
                LA, Ll = bSort(A[:k], 1, l)
                RA, Rl = bSort(A[k:], 0, l)
                m.d.comb += sum(([bv.eq(av), bi.eq(ai)] for (bv, bi), (av, ai) in zip(B, LA + RA)), start=[])
                return bMerge(B, d, max(Ll, Rl))
    
        def bMerge(A, d, l=0):
            cnt = len(A)
            if cnt > 1:
                k = cnt//2
                B = [(Signal(), Signal(W)) for _ in range(len(A))]
                for i in range(0, k):
                    S = swap2(A[i], A[i+k], d)
                    m.d.comb += [
                    B[i][0].eq(S[0][0]),
                    B[i][1].eq(S[0][1]),
                    B[i+k][0].eq(S[1][0]),
                    B[i+k][1].eq(S[1][1])]
                l += 1
                if l in self.registers:
                        C = [(Signal(), Signal(W)) for _ in range(len(B))]
                        s = regLayers.get(l,None)

                        v_b, e_b = zip(*C)
                        v_a, e_a = zip(*B)

                        if s == None:
                            regLayers[l] = e_a, v_a, e_b, v_b
                        else:
                            aE, aV, bE, bV = s
                            regLayers[l] = aE+e_a, aV+v_a, bE+e_b, bV+v_b
                        B = C
                LB, Ll = bMerge(B[:k], d, l)
                RB, Rl = bMerge(B[k:], d, l)
                return LB+RB, max(Ll, Rl)
            return A, l

        if self.stable and self.index_in:
            cw = cl2(self.N)
            I = [(v, Cat(self.indexes_in[i], Const(i, cw))) for i,v in enumerate(self.valid_i)]
        else:
            I = [(v, self.indexes_in[i]) for i,v in enumerate(self.valid_i)]
        
        diff = (1 << cl2(self.N, min1=False)) - self.N

        if self.N > max(perfectSortings.keys()):
            I.extend((Const(0, 1), Const(0, W)) for _ in range(diff))

        res, layers = bSort(I, self.dir)

        if len(self.registers) > 0:

            ready = self.ready_o
            if self.optimized_valid_in:
                o_valid = self.o_valid_in
            
            first = self.registers[0]
            last = self.registers[-1]
            for l in self.registers:
                aE, aV, bE, bV = regLayers[l]

                m.submodules[f"reg{l}"] = reg = StreamReg(T=BasicStreamInterface, payload_width=len(aE)*W, valid_width=len(aV), optimized_valid_in=self.optimized_valid_in or l > first, optimized_valid_out=self.optimized_valid_out or l < last)
                m.d.comb += ready.eq(reg.si.ready)

                if "o_valid" in reg.si.fields:
                    m.d.comb += reg.si.o_valid.eq(o_valid)
                if "o_valid" in reg.so.fields:
                    o_valid = reg.so.o_valid

                for i in range(len(aV)):
                    m.d.comb += [
                        reg.si.payload.word_select(i, W).eq(aE[i]),
                        reg.si.valid[i].eq(aV[i]),
                        bE[i].eq(reg.so.payload.word_select(i, W)),
                        bV[i].eq(reg.so.valid[i])
                    ]
                ready = reg.so.ready
            m.d.comb += ready.eq(self.ready_i)
            if self.optimized_valid_out:
                m.d.comb += self.o_valid_out.eq(o_valid)

        if self.dir:
            res = res[diff:]
        else:
            res = res[:self.N]

        for i, (v, i_o) in enumerate(res):
            m.d.comb += [
                self.valid_o[i].eq(v),
                self.indexes[i].eq(i_o[:self.width])
            ]

        return m

class StreamCompaction(Elaboratable):

    def __init__(self, N=3, W=8):
        self.N = N
        self.W = W

        self.input_stream = BasicStreamInterface(payload_width=self.N*self.W, valid_width=self.N)
        self.output_stream = BasicStreamInterface(payload_width=self.N*self.W, valid_width=self.N)

    def elaborate(self, platform):

        m = Module()

        if m.setPureIdentifier(type(self),self.N, self.W):
            m.submodules += Instance("dummy",
            i_inputstream_valid=self.input_stream.valid, i_inputstream_payload=self.input_stream.payload, i_outputstream_ready=self.output_stream.ready,
            o_outputstream_valid=self.output_stream.valid, o_outputstream_payload=self.output_stream.payload, o_inputstream_ready=self.input_stream.ready)
            return m
        
        print("Elaborating ", self.__class__.__name__, self)

        m.submodules.indx = indx = CompactionIndexes(self.N, 0, False)
        m.d.comb += [
            self.input_stream.ready.eq(self.output_stream.ready),
            indx.valid_i.eq(self.input_stream.valid),
            self.output_stream.valid.eq(indx.valid_o)
        ]
        input_values = Array(self.input_stream.payload.word_select(i, self.W) for i in range(self.N))
        m.d.comb += [self.output_stream.payload.word_select(i, self.W).eq(input_values[indx.indexes[i]]) for i in range(self.N)]

        return m

