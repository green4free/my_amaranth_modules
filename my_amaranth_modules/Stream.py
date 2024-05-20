from amaranth import *
from amlib.stream import StreamInterface
from amaranth.tracer import get_var_name
from typing import Hashable
from amaranth.lib.data import *
from amaranth.hdl.ast import ShapeCastable
from amaranth.lib.fifo import SyncFIFO

from amaranth.asserts import Assert, Assume, Cover
from amaranth.sim import Simulator, Delay, Settle, Tick

from fhdl import FHDLTestCase

from utils import ifGen

class BasicStreamInterface(StreamInterface, Record):
    
    def __init__(self, *, name=None, payload_width=8, valid_width=1, extra_fields=None, src_loc_at=0):

        # If we don't have any extra fields, use an empty list in its place.
        if extra_fields is None:
            extra_fields = []

        # ... store our extra fields...
        self._extra_fields = [n for n, width in extra_fields]

        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        # ... and create our basic stream.
        Record.__init__(self,[
            ('valid',    valid_width),
            ('ready',    1),
            ('payload',  payload_width),
            *extra_fields
        ], name=new_name)
    
    def attach(self, interface, omit=None):
        # Create lists of fields to be copied -to- the interface (RHS fields),
        # and lists of fields to be copied -from- the interface (LHS fields).
        rhs_fields = ['valid', 'payload', *self._extra_fields]
        lhs_fields = ['ready']
        assignments = []

        if omit:
            rhs_fields = [field for field in rhs_fields if field not in omit]
            lhs_fields = [field for field in lhs_fields if field not in omit]


        # Create each of our assignments.
        for field in rhs_fields:
            assignment = interface[field].eq(self[field])
            assignments.append(assignment)
        for field in lhs_fields:
            assignment = self[field].eq(interface[field])
            assignments.append(assignment)

        return assignments



class ArrayStreamInterface(StreamInterface, Record):
    
    def __init__(self, *, name=None, payload_width=8, valid_width=1, extra_fields=None, src_loc_at=0):

        # If we don't have any extra fields, use an empty list in its place.
        if extra_fields is None:
            extra_fields = []

        self.N = valid_width
        # ... store our extra fields...
        self._extra_fields = [n for n, e_layout in extra_fields]
        for n, e_layout in extra_fields:
            assert isinstance(e_layout, ShapeCastable) or isinstance(e_layout, Shape) or isinstance(e_layout, int), f"{e_layout}"

        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        # ... and create our basic stream.
        Record.__init__(self,[
            ('valid',    valid_width),
            ('ready',    1),
            *((f'payload{n}',  payload_width) for n in range(valid_width)),
            *extra_fields
            ], name=new_name)
    
    def __getattr__(self, name):

        # Allow "payload" to access all the payload fields as an array
        if name == "payload":
            return Array(self[f'payload{n}'] for n in range(len(self.valid)))
        return super().__getattr__(name)
    
    def attach(self, interface, omit=None):
        # Create lists of fields to be copied -to- the interface (RHS fields),
        # and lists of fields to be copied -from- the interface (LHS fields).
        rhs_fields = [f for f in self._extra_fields] + ['valid']
        lhs_fields = ['ready']
        assignments = []

        if 'payload' in interface.fields:
            rhs_fields.append('payload')
        else:
            rhs_fields += [f'payload{n}' for n in range(len(self.valid))]

        if omit:
            if isinstance(omit, str):
                omit = [omit]
            else:
                omit = list(omit)
            if "payload" in omit:
                omit += [f'payload{n}' for n in range(len(self.valid))]
            rhs_fields = [field for field in rhs_fields if field not in omit]
            lhs_fields = [field for field in lhs_fields if field not in omit]

        # Create each of our assignments.
        for field in rhs_fields:
            if field == 'payload':
                assignment = interface[field].eq(Cat(*self[field]))
            else:
                assignment = interface[field].eq(self[field])
            assignments.append(assignment)
        for field in lhs_fields:
            assignment = self[field].eq(interface[field])
            assignments.append(assignment)

        return assignments


class StreamReg(Elaboratable):

    def __init__(self, T=StreamInterface, payload_width=8, valid_width=1, zero_payload_at_nv=False, use_double_buffering=True, max_width=256, optimized_valid_in=False, optimized_valid_out=False, extra_fields=[]):
        assert(T in [StreamInterface, BasicStreamInterface, ArrayStreamInterface])
        
        self.T_ = {StreamInterface:0, BasicStreamInterface:1, ArrayStreamInterface:2}[T]

        self.max_width = max_width
        self.optimized_valid_in = optimized_valid_in
        self.optimized_valid_out = optimized_valid_out
        self.si = T(name="si", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_in else [])+extra_fields)
        self.so = T(name="so", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_out else [])+extra_fields)
        self.zero_payload_at_nv = zero_payload_at_nv
        self.payload_width = payload_width
        self.valid_width = valid_width
        self.use_double_buffering = use_double_buffering
        self.ivalid = Signal()

    def ports(self):
        return [self.si[f] for f in self.si.fields] + [self.so[f] for f in self.so.fields]

    def elaborate(self, platform):

        m = Module()

        data_in = [field for field in self.si.fields if field not in ["valid", "ready"]]
        data_out = [field for field in self.so.fields if field not in ["valid", "ready"]]

        if m.setPureIdentifier(type(self), type(self.si), self.T_, tuple(self.si._extra_fields), self.max_width, self.zero_payload_at_nv, self.payload_width, self.valid_width, self.use_double_buffering, self.optimized_valid_in, self.optimized_valid_out):
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"),
            o_ivalid=self.ivalid,
            i_si_valid=self.si.valid, o_si_ready=self.si.ready,
            o_so_valid=self.so.valid, i_so_ready=self.so.ready,
            **{f"i_si_{f}":self.si[f] for f in data_in},
            **{f"o_so_{f}":self.so[f] for f in data_out})
            return m
        
        print("Elaborating ", self.__class__.__name__, self)


        for field in self.so.fields:
            if field not in ["valid", "ready"]:
                self.so[field].reset_less = True

        if self.optimized_valid_in:
            m.d.comb += self.ivalid.eq(self.si.o_valid)
            ovalid = Signal()
        elif self.valid_width == 1:
            m.d.comb += self.ivalid.eq(self.si.valid)
            ovalid = self.so.valid
        else:
            m.d.comb += self.ivalid.eq(self.si.valid.any())
            ovalid = Signal()
        
        active_ovalid = self.optimized_valid_in or (self.valid_width > 1)

        if self.optimized_valid_out:
            m.d.comb += self.so.o_valid.eq(ovalid)

        
        buffer = []
        outputs = []
        inputs = []

        for f in self.si.fields:
            
            if f in ["valid", "ready", "o_valid"]:
                continue

            assert f in self.so.fields
            
            f_len = len(self.si[f])
            if (self.max_width < 1) or (f_len <= self.max_width):
                inputs.append(self.si[f])
                outputs.append(self.so[f])
                buffer.append(Signal(f_len, name=f"buffer_{f}"))
                continue
            indexes = []
            ind = 0
            while ind < f_len:
                indexes.append(ind)
                ind += self.max_width
            indexes.append(ind)
            for i in range(len(indexes)-1):
                i0 = indexes[i]
                i1 = indexes[i+1]
                buffer.append(Signal(i1-i0, name=f"buffer_{f}{i}"))
                o = Signal(i1-i0, name=f"output_{f}{i}")
                m.d.comb += self.so[f][i0:i1].eq(o)
                outputs.append(o)
                input_S = Signal(i1-i0, name=f"input_{f}{i}")
                m.d.comb += input_S.eq(self.si[f][i0:i1])
                inputs.append(input_S)
            
        if self.use_double_buffering:
            buffer_valid = Signal(self.valid_width)

            ready = Signal()
            m.d.comb += ready.eq(self.so.ready | ~(ovalid))

            if self.optimized_valid_in:
                bv = Signal()
            elif self.valid_width==1:
                bv = buffer_valid
            else:
                bv = Signal()

            with m.If(ready & bv): #Shouldn't buffer_valid/bv be zeroed here
                    m.d.sync += [self.so.valid.eq(buffer_valid)] + [outputs[i].eq(buffer[i]) for i in range(len(buffer))]
                    if active_ovalid:
                        m.d.sync += ovalid.eq(1)
            with m.Elif(ready & self.ivalid):
                    m.d.sync += [self.so.valid.eq(self.si.valid)]  + [outputs[i].eq(inputs[i]) for i in range(len(inputs))]
                    if active_ovalid:
                        m.d.sync += ovalid.eq(1)
            with m.Elif(self.so.ready):
                m.d.sync += self.so.valid.eq(0)
                if active_ovalid:
                    m.d.sync += ovalid.eq(0)
                if self.zero_payload_at_nv:
                    m.d.sync += [outputs[i].eq(0) for i in range(len(outputs))]

            with m.If(self.ivalid & ~bv & ~ready):
                m.d.sync += [buffer_valid.eq(self.si.valid)] + [buffer[i].eq(inputs[i]) for i in range(len(inputs))]
                if active_ovalid:
                    m.d.sync += bv.eq(1)
            with m.Elif(ready):
                m.d.sync += buffer_valid.eq(0)
                if active_ovalid:
                    m.d.sync += bv.eq(0)
            
            m.d.comb += self.si.ready.eq(~bv)

        else:

            del buffer

            ready = Signal()
            m.d.comb += ready.eq(self.so.ready | ~(ovalid))
            m.d.comb += self.si.ready.eq(ready)
            with m.If(ready & self.ivalid):
                m.d.sync += [self.so.valid.eq(self.si.valid)]  + [outputs[i].eq(inputs[i]) for i in range(len(inputs))]
                if active_ovalid:
                    m.d.sync += ovalid.eq(1)
            with m.Elif(self.so.ready):
                m.d.sync += self.so.valid.eq(0)
                if active_ovalid:
                    m.d.sync += ovalid.eq(0)
                if self.zero_payload_at_nv:
                    m.d.sync += [outputs[i].eq(0) for i in range(len(outputs))]
        

        if platform=="formal":
            started = Signal(reset_less=True, reset=0)
            m.d.sync += started.eq(1)

            rst = ResetSignal("sync")

            past_si_payload = Signal(len(self.si.payload))
            m.d.sync += past_si_payload.eq(self.si.payload)

            past_input_valid_and_not_ready = Signal()
            m.d.sync += past_input_valid_and_not_ready.eq(self.ivalid & ~self.si.ready)

            last_rest = Signal(reset_less=True)
            m.d.sync += last_rest.eq(rst)
            with m.If(last_rest | ~rst):
                m.d.sync += Assume(~rst)

            with m.If(~started):
                m.d.sync += Assume(~self.ivalid)
            with m.Elif(past_input_valid_and_not_ready):
                m.d.sync += Assume(self.ivalid & (self.si.payload == past_si_payload))

            past_output_valid_and_not_ready = Signal()
            m.d.sync += past_output_valid_and_not_ready.eq(ovalid & ~self.so.ready)

            past_so_payload = Signal(len(self.so.payload))
            m.d.sync += past_so_payload.eq(self.so.payload)

            with m.If(~started):
                m.d.sync += Assert(~ovalid)
            with m.Elif(past_output_valid_and_not_ready):
                m.d.sync += Assert(ovalid & (self.so.payload == past_so_payload))
            
            past_input_transfere_and_full = Signal()
            m.d.sync += past_input_transfere_and_full.eq(self.ivalid & self.si.ready & ovalid & (bv if self.use_double_buffering else Const(1)))
            with m.If(started & past_input_transfere_and_full & ~self.so.ready):
                m.d.sync += Assert(~self.si.ready)
            
            if self.use_double_buffering:
                with m.If(started & ~bv):
                    m.d.sync += Assert(self.si.ready)
                
                past_iv = Signal()
                m.d.sync += past_iv.eq(self.ivalid)
                past_bv = Signal()
                m.d.sync += past_bv.eq(bv)
                past_from_b_transfere = Signal()
                m.d.sync += past_from_b_transfere.eq(past_bv & ~ovalid & ~self.ivalid)
                with m.If(started & past_from_b_transfere & ~self.ivalid):
                    m.d.sync += Assert(~bv)

        return m

class StreamFifo(Elaboratable):
    def __init__(self, T=BasicStreamInterface, payload_width=8, valid_width=1, depth=32, extra_fields=None, memAttrs=None):
        assert(T in [StreamInterface, BasicStreamInterface, ArrayStreamInterface])

        extra_fields = extra_fields or []

        self.si = T(name="si", payload_width=payload_width, valid_width=valid_width, extra_fields=extra_fields)
        self.so = T(name="so", payload_width=payload_width, valid_width=valid_width, extra_fields=extra_fields)
        self.stream_config = {"T":T, "payload_width":payload_width, "valid_width":valid_width, "extra_fields":extra_fields}
        self.payload_width = payload_width
        self.valid_width = valid_width
        self.depth = depth
        self.fill = Signal(range(self.depth+1))
        self.memAttrs = memAttrs

    def elaborate(self, platform):
        m = Module()

        if m.setPureIdentifier(type(self), type(self.si), tuple(self.si._extra_fields), self.payload_width, self.valid_width, self.depth, tuple(self.memAttrs.items()) if isinstance(self.memAttrs, dict) else self.memAttrs):
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"),
            o_si_ready=self.si.ready, i_so_ready=self.so.ready, o_fill=self.fill,
            **{f"i_si_{f}":self.si[f] for f in self.si.fields if f != "ready"},
            **{f"o_so_{f}":self.so[f] for f in self.so.fields if f != "ready"})
            return m
        
        print("Elaborating ", self.__class__.__name__, self)

        valid = self.si.valid if self.valid_width <= 1 else self.si.valid.any()
        removed_fields = ["ready"]
        if self.valid_width <= 1:
            removed_fields.append("valid")
        

        m.submodules.ouput_reg = output_reg = StreamReg(optimized_valid_in=(self.valid_width > 1),**self.stream_config, use_double_buffering=False)

        data_in = Cat(*[self.si[field] for field in self.si.fields if field not in removed_fields])
        data_out = Cat(*[output_reg.si[field] for field in output_reg.si.fields if field not in removed_fields])
        m.d.comb += self.so.stream_eq(output_reg.so)

        m.submodules.fifo = fifo = SyncFIFO(width=len(data_in), depth=self.depth, fwft=False, memAttrs=self.memAttrs)

        m.d.comb += [
            self.fill.eq(fifo.level),
            fifo.w_data.eq(data_in),
            fifo.w_en.eq(valid),
            self.si.ready.eq(fifo.w_rdy),
            data_out.eq(fifo.r_data)
        ]

        ready = Signal()
        valid_out = Signal()
        m.d.comb += ready.eq(output_reg.si.ready | ~valid_out)

        if self.valid_width <= 1:
            m.d.comb += output_reg.si.valid.eq(valid_out)
        else:
            m.d.comb += output_reg.si.o_valid.eq(valid_out)

        m.d.comb += fifo.r_en.eq(ready)
        
        with m.If(fifo.r_rdy & ready):
            m.d.sync += valid_out.eq(1)
        with m.Elif(output_reg.si.ready):
            m.d.sync += valid_out.eq(0)
        
        return m


class StreamJoin(Elaboratable):

    def __init__(self, T=StreamInterface, payload_width=8, valid_width=1, max_width=256, optimized_valid_in=False, optimized_valid_out=False, extra_fields=[], fixed_prio=False):
        assert(T in [StreamInterface, BasicStreamInterface, ArrayStreamInterface])

        self.max_width = max_width
        self.optimized_valid_in = optimized_valid_in
        self.optimized_valid_out = optimized_valid_out
        self.si = [T(name=f"si{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_in else [])+extra_fields) for i in range(2)]
        self.so = T(name="so", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_out else [])+extra_fields)
        self.payload_width = payload_width
        self.valid_width = valid_width
        self.fixed_prio = fixed_prio
        self.w_prioCounter = "prioCounter" in [e[0] for e in extra_fields]

    def ports(self):
        return [self.si[f] for f in self.si.fields] + [self.so[f] for f in self.so.fields]

    def elaborate(self, platform):

        m = Module()

        data_in = [[field for field in si.fields if field not in ["ready"]] for si in self.si]
        data_out = [field for field in self.so.fields if field not in ["ready"]]

        if m.setPureIdentifier(type(self), type(self.so), tuple(self.so._extra_fields), self.max_width, self.payload_width, self.valid_width, self.optimized_valid_in, self.optimized_valid_out, self.fixed_prio, self.w_prioCounter):
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"),
            o_si0_ready=self.si[0].ready, o_si1_ready=self.si[1].ready, i_so_ready=self.so.ready,
            **{f"i_si0_{f}":self.si[0][f] for f in data_in[0]},
            **{f"i_si1_{f}":self.si[1][f] for f in data_in[1]},
            **{f"o_so_{f}":self.so[f] for f in data_out})
            return m
        
        print("Elaborating ", self.__class__.__name__, self)
        
        for field in self.so.fields:
            if field not in ["valid", "ready"]:
                self.so[field].reset_less = True

        if self.optimized_valid_in:
            ivalid = [si.o_valid for si in self.si]
            ovalid = Signal()
        elif self.valid_width == 1:
            ivalid = [si.valid for si in self.si]
            ovalid = self.so.valid
        else:
            ivalid = [Signal(name=f"ivalid{i}") for i in range(2)]
            m.d.comb += [iv.eq(si.valid.any()) for iv, si in zip(ivalid, self.si)]
            ovalid = Signal()
        
        active_ovalid = self.optimized_valid_in or (self.valid_width > 1)

        if self.optimized_valid_out:
            m.d.comb += self.so.o_valid.eq(ovalid)

        
        buffer = []
        outputs = []
        inputs = [[], []]

        for f in self.so.fields:
            
            if f in ["valid", "ready", "o_valid"]:
                continue

            assert f in self.si[0].fields and f in self.si[1].fields
            
            f_len = len(self.so[f])
            if (self.max_width < 1) or (f_len <= self.max_width):
                inputs[0].append(self.si[0][f])
                inputs[1].append(self.si[1][f])
                outputs.append(self.so[f])
                buffer.append(Signal(f_len, name=f"buffer_{f}"))
                continue
            indexes = []
            ind = 0
            while ind < f_len:
                indexes.append(ind)
                ind += self.max_width
            indexes.append(ind)
            for i in range(len(indexes)-1):
                i0 = indexes[i]
                i1 = indexes[i+1]
                buffer.append(Signal(i1-i0, name=f"buffer_{f}{i}"))
                o = Signal(i1-i0, name=f"output_{f}{i}")
                m.d.comb += self.so[f][i0:i1].eq(o)
                outputs.append(o)
                input0_S = Signal(i1-i0, name=f"input0_{f}{i}")
                m.d.comb += input0_S.eq(self.si[0][f][i0:i1])
                inputs[0].append(input0_S)
                input1_S = Signal(i1-i0, name=f"input1_{f}{i}")
                m.d.comb += input1_S.eq(self.si[1][f][i0:i1])
                inputs[1].append(input1_S)
        

        buffer_valid = Signal(self.valid_width)
        ready = Signal()
        if self.optimized_valid_in:
            bv = Signal()
        elif self.valid_width==1:
            bv = buffer_valid
        else:
            bv = Signal()
        

        m.d.comb += ready.eq(self.so.ready | ~ovalid)

        if self.fixed_prio:
            m.d.comb += self.si[0].ready.eq(ready )
            m.d.comb += self.si[1].ready.eq(ready & (~bv))
        else:
            rr_prio = Signal()
            m.d.comb += [
                self.si[0].ready.eq(ready & ((rr_prio==0) | ~bv)),
                self.si[1].ready.eq(ready & ((rr_prio==1) | ~bv))
            ]
            if self.w_prioCounter:
                m.d.comb += rr_prio.eq(self.si[1].prioCounter > self.si[0].prioCounter)
        
        with m.If(ready & bv):
            m.d.sync += [ovalid.eq(1)] + [
                o.eq(b) for o, b in zip(outputs, buffer)
            ]
            if self.valid_width > 1:
                m.d.sync += self.so.valid.eq(buffer_valid)
            for i, ifTransfer in enumerate(ifGen(m, (self.si[i].ready & ivalid[i] for i in range(2)), withElse=False, startFromIf=True)):
                with ifTransfer:
                    m.d.sync += bv.eq(1)
                    m.d.sync += [b.eq(inp) for b, inp in zip(buffer, inputs[i])]
                    if (not self.fixed_prio) and (not self.w_prioCounter):
                        m.d.sync += rr_prio.eq(Mux(ivalid[not i], not i, i))
                    if self.valid_width > 1:
                        m.d.sync += buffer_valid.eq(self.si[i].valid)
            with m.Else():
                m.d.sync += bv.eq(0)
        
        for i, ifTransfer in enumerate(ifGen(m, (self.si[i].ready & ivalid[i] for i in range(2)), withElse=False, startFromIf=False)):
            with ifTransfer:
                m.d.sync += [ovalid.eq(1)] + [
                    o.eq(inp) for o, inp in zip(outputs, inputs[i])
                ]
                if self.valid_width > 1:
                    m.d.sync += self.so.valid.eq(self.si[i].valid)
                with m.If(self.si[not i].ready & ivalid[not i]):
                    m.d.sync += bv.eq(1)
                    m.d.sync += [b.eq(inp) for b, inp in zip(buffer, inputs[not i])]
                    if (not self.fixed_prio) and (not self.w_prioCounter):
                        m.d.sync += rr_prio.eq(Mux(ivalid[i], i, not i))
                    if self.valid_width > 1:
                        m.d.sync += buffer_valid.eq(self.si[not i].valid)
        
        with m.Elif(self.so.ready):
            m.d.sync += self.so.valid.eq(0)
        
        return m

class StreamJoin2(Elaboratable):

    def __init__(self, T=StreamInterface, payload_width=8, valid_width=1, max_width=256, optimized_valid_in=False, optimized_valid_out=False, extra_fields=[]):
        assert(T in [StreamInterface, BasicStreamInterface, ArrayStreamInterface])

        self.max_width = max_width
        self.optimized_valid_in = optimized_valid_in
        self.optimized_valid_out = optimized_valid_out
        self.si = [T(name=f"si{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_in else [])+extra_fields) for i in range(2)]
        self.so = T(name="so", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_out else [])+extra_fields)
        self.payload_width = payload_width
        self.valid_width = valid_width
        self.extra_fields = extra_fields
        self.w_prioCounter = "prioCounter" in [e[0] for e in extra_fields]

    def ports(self):
        return [self.si[f] for f in self.si.fields] + [self.so[f] for f in self.so.fields]

    def elaborate(self, platform):
        
        assert self.w_prioCounter

        m = Module()

        data_in = [[field for field in si.fields if field not in ["ready"]] for si in self.si]
        data_out = [field for field in self.so.fields if field not in ["ready"]]

        if m.setPureIdentifier(type(self), type(self.so), tuple(self.so._extra_fields), self.max_width, self.payload_width, self.valid_width, self.optimized_valid_in, self.optimized_valid_out, self.w_prioCounter):
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"),
            o_si0_ready=self.si[0].ready, o_si1_ready=self.si[1].ready, i_so_ready=self.so.ready,
            **{f"i_si0_{f}":self.si[0][f] for f in data_in[0]},
            **{f"i_si1_{f}":self.si[1][f] for f in data_in[1]},
            **{f"o_so_{f}":self.so[f] for f in data_out})
            return m
        
        print("Elaborating ", self.__class__.__name__, self)


        m.submodules.ireg0 = ireg0 = StreamReg(type(self.si[0]), self.payload_width, self.valid_width, False, False, self.max_width, self.optimized_valid_in, True, self.extra_fields)
        m.submodules.ireg1 = ireg1 = StreamReg(type(self.si[0]), self.payload_width, self.valid_width, False, False, self.max_width, self.optimized_valid_in, True, self.extra_fields)
        
        m.d.comb += [
            ireg0.si.stream_eq(self.si[0]),
            ireg1.si.stream_eq(self.si[1])
        ]

        for field in self.so.fields:
            if field not in ["valid", "ready"]:
                self.so[field].reset_less = True

        if self.optimized_valid_in:
            ovalid = Signal()
        elif self.valid_width == 1:
            ovalid = self.so.valid
        else:
            ovalid = Signal()

        active_ovalid = self.optimized_valid_in or (self.valid_width > 1)

        if self.optimized_valid_out:
            m.d.comb += self.so.o_valid.eq(ovalid)
        
        i_si = [ireg0.so, ireg1.so]

        outputs = []
        inputs = [[], []]

        for f in self.so.fields:
            
            if f in ["valid", "ready", "o_valid"]:
                continue

            assert f in i_si[0].fields and f in i_si[1].fields
            
            f_len = len(self.so[f])
            if (self.max_width < 1) or (f_len <= self.max_width):
                inputs[0].append(i_si[0][f])
                inputs[1].append(i_si[1][f])
                outputs.append(self.so[f])
                continue
            indexes = []
            ind = 0
            while ind < f_len:
                indexes.append(ind)
                ind += self.max_width
            indexes.append(ind)
            for i in range(len(indexes)-1):
                i0 = indexes[i]
                i1 = indexes[i+1]
                o = Signal(i1-i0, name=f"output_{f}{i}")
                m.d.comb += self.so[f][i0:i1].eq(o)
                outputs.append(o)
                input0_S = Signal(i1-i0, name=f"input0_{f}{i}")
                m.d.comb += input0_S.eq(i_si[0][f][i0:i1])
                inputs[0].append(input0_S)
                input1_S = Signal(i1-i0, name=f"input1_{f}{i}")
                m.d.comb += input1_S.eq(i_si[1][f][i0:i1])
                inputs[1].append(input1_S)
        



        ready = Signal()
        m.d.comb += ready.eq(self.so.ready | ~ovalid)
        rr_prio = Signal()
        last_rr_prio = Signal(10, reset=1)
        
        m.d.comb += [
            i_si[0].ready.eq(ready & ((rr_prio==0))),
            i_si[1].ready.eq(ready & ((rr_prio==1)))
        ]

        with m.If(ready):
            with m.If(ireg0.ivalid & ireg1.ivalid):
                m.d.sync += last_rr_prio.eq(Cat(rr_prio, *(last_rr_prio[:9])))
                with m.If(last_rr_prio.all() | ~(last_rr_prio.any())):
                    m.d.sync += rr_prio.eq(~rr_prio)
                with m.Elif(ireg1.si.prioCounter == ireg0.si.prioCounter):
                    m.d.sync += rr_prio.eq(Mux(rr_prio, 0, ~last_rr_prio[0]))
                with m.Else():
                    m.d.sync += rr_prio.eq(ireg1.si.prioCounter > ireg0.si.prioCounter)
            with m.Elif(ireg0.ivalid):
                m.d.sync += rr_prio.eq(0)
            with m.Elif(ireg1.ivalid):
                m.d.sync += rr_prio.eq(1)
            with m.Else():
                m.d.sync += rr_prio.eq(0)
        
        with m.If(i_si[0].ready & i_si[0].o_valid):
            m.d.sync += [self.so.valid.eq(i_si[0].valid)]  + [outputs[i].eq(inputs[0][i]) for i in range(len(outputs))]
            if active_ovalid:
                m.d.sync += ovalid.eq(1)
        with m.Elif(i_si[1].ready & i_si[1].o_valid):
            m.d.sync += [self.so.valid.eq(i_si[1].valid)]  + [outputs[i].eq(inputs[1][i]) for i in range(len(outputs))]
            if active_ovalid:
                m.d.sync += ovalid.eq(1)
        with m.Elif(self.so.ready):
            m.d.sync += self.so.valid.eq(0)
            if active_ovalid:
                m.d.sync += ovalid.eq(0)
        
        return m

class StreamDistribute_2to2(Elaboratable):

    def __init__(self, T=StreamInterface, payload_width=8, valid_width=1, max_width=256, optimized_valid_in=False, optimized_valid_out=False, extra_fields=[]):
        assert(T in [StreamInterface, BasicStreamInterface, ArrayStreamInterface])

        self.max_width = max_width
        self.optimized_valid_in = optimized_valid_in
        self.optimized_valid_out = optimized_valid_out
        self.si = [T(name=f"si{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_in else [])+extra_fields) for i in range(2)]
        self.so = [T(name=f"so{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_out else [])+extra_fields) for i in range(2)]
        self.payload_width = payload_width
        self.valid_width = valid_width


    def ports(self):
        return sum([[s[f] for f in s.fields] for s in self.si + self.so], [])

    def elaborate(self, platform):

        m = Module()

        data_in = [[field for field in si.fields if field not in ["ready"]] for si in self.si]
        data_out = [[field for field in so.fields if field not in ["ready"]] for so in self.so]

        if m.setPureIdentifier(type(self), type(self.si[0]), tuple(self.si[0]._extra_fields), self.max_width, self.payload_width, self.valid_width, self.optimized_valid_in, self.optimized_valid_out):
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"),
            o_si0_ready=self.si[0].ready, o_si1_ready=self.si[1].ready,
            i_so0_ready=self.so[0].ready, i_so1_ready=self.so[1].ready,
            **{f"i_si0_{f}":self.si[0][f] for f in data_in[0]},
            **{f"i_si1_{f}":self.si[1][f] for f in data_in[1]},
            **{f"o_so0_{f}":self.so[0][f] for f in data_out[0]},
            **{f"o_so1_{f}":self.so[1][f] for f in data_out[1]}
            )
            return m
        
        print("Elaborating ", self.__class__.__name__, self)
        
        for so in self.so:
            for field in so.fields:
                if field not in ["valid", "ready"]:
                    so[field].reset_less = True

        if self.optimized_valid_in:
            ivalid = [si.o_valid for si in self.si]
            ovalid = [Signal(name=f"ovalid{i}") for i in range(2)]
        elif self.valid_width == 1:
            ivalid = [si.valid for si in self.si]
            ovalid = [self.so[i].valid for i in range(2)]
        else:
            ivalid = [Signal(name=f"ivalid{i}") for i in range(2)]
            m.d.comb += [iv.eq(si.valid.any()) for iv, si in zip(ivalid, self.si)]
            ovalid = [Signal(name=f"ovalid{i}") for i in range(2)]
        
        active_ovalid = self.optimized_valid_in or (self.valid_width > 1)

        if self.optimized_valid_out:
            m.d.comb += [self.so[i].o_valid.eq(ovalid[i]) for i in range(2)]

        
        buffer = []
        outputs = [[], []]
        inputs = [[], []]

        for f in self.si[0].fields:
            
            if f in ["valid", "ready", "o_valid"]:
                continue

            assert f in self.si[0].fields and f in self.si[1].fields
            
            f_len = len(self.si[0][f])
            if (self.max_width < 1) or (f_len <= self.max_width):
                inputs[0].append(self.si[0][f])
                inputs[1].append(self.si[1][f])
                outputs[0].append(self.so[0][f])
                outputs[1].append(self.so[1][f])
                buffer.append(Signal(f_len, name=f"buffer_{f}"))
                continue
            indexes = []
            ind = 0
            while ind < f_len:
                indexes.append(ind)
                ind += self.max_width
            indexes.append(ind)
            for i in range(len(indexes)-1):
                i0 = indexes[i]
                i1 = indexes[i+1]
                buffer.append(Signal(i1-i0, name=f"buffer_{f}{i}"))
                for ii in range(2):
                    o = Signal(i1-i0, name=f"output{ii}_{f}{i}")
                    m.d.comb += self.so[ii][f][i0:i1].eq(o)
                    outputs[ii].append(o)
                    input_S = Signal(i1-i0, name=f"input{ii}_{f}{i}")
                    m.d.comb += input_S.eq(self.si[ii][f][i0:i1])
                    inputs[ii].append(input_S)
        

        buffer_valid = Signal(self.valid_width)
        ready = [Signal(name=f"ready{i}") for i in range(2)]
        m.d.comb += [ready[i].eq(self.so[i].ready | ~(ovalid[i])) for i in range(2)]
        if self.optimized_valid_in:
            bv = Signal()
        elif self.valid_width==1:
            bv = buffer_valid
        else:
            bv = Signal()
        
        rr_prio = Signal()

        m.d.comb += [
            self.si[0].ready.eq((ready[0] | ready[1]) & ((rr_prio==0) | ~bv)),
            self.si[1].ready.eq((ready[0] | ready[1]) & ((rr_prio==1) | ~bv))
        ]
        
        used = Signal(3)
        m.d.comb += used.eq(0)
        with m.If(ready[0] & bv):
            m.d.comb += used[2].eq(1)
            m.d.sync += [ovalid[0].eq(1)] + [
                o.eq(b) for o, b in zip(outputs[0], buffer)
            ]
            if self.valid_width > 1:
                m.d.sync += self.so[0].valid.eq(buffer_valid)
            for i, ifTransfer in enumerate(ifGen(m, (self.si[i].ready & ivalid[i] & ~ready[1] for i in range(2)), withElse=False, startFromIf=True)):
                with ifTransfer:
                    m.d.comb += used[i].eq(1)
                    m.d.sync += [
                        bv.eq(1),
                        rr_prio.eq(Mux(ivalid[not i], not i, i))
                    ] + [b.eq(inp) for b, inp in zip(buffer, inputs[i])]
                    if self.valid_width > 1:
                        m.d.sync += buffer_valid.eq(self.si[i].valid)
            with m.Else():
                m.d.sync += bv.eq(0)
        
        for i, ifTransfer in enumerate(ifGen(m, (self.si[i].ready & ivalid[i] for i in range(2)), withElse=False, startFromIf=False)):
            with ifTransfer:
                m.d.comb += used[i].eq(1)
                m.d.sync += [ovalid[0].eq(1)] + [
                    o.eq(inp) for o, inp in zip(outputs[0], inputs[i])
                ]
                if self.valid_width > 1:
                    m.d.sync += self.so.valid.eq(self.si[i].valid)
                with m.If(self.si[not i].ready & ivalid[not i] & ~ready[1]):
                    m.d.comb += used[not i].eq(1)
                    m.d.sync += [
                        bv.eq(1),
                        rr_prio.eq(Mux(ivalid[i], i, not i))
                    ] + [b.eq(inp) for b, inp in zip(buffer, inputs[not i])]
                    if self.valid_width > 1:
                        m.d.sync += buffer_valid.eq(self.si[not i].valid)
        
        with m.Elif(self.so[0].ready):
            m.d.sync += self.so[0].valid.eq(0)
        
        with m.If(ready[1] & bv & ~used[2]):
            m.d.sync += [ovalid[1].eq(1)] + [
                o.eq(b) for o, b in zip(outputs[1], buffer)
            ]
            if self.valid_width > 1:
                m.d.sync += self.so[1].valid.eq(buffer_valid)
            for i, ifTransfer in enumerate(ifGen(m, (self.si[i].ready & ivalid[i] & ~used[i] for i in range(2)), withElse=False, startFromIf=True)):
                with ifTransfer:
                    m.d.sync += [
                        bv.eq(1),
                        rr_prio.eq(Mux(ivalid[not i], not i, i))
                    ] + [b.eq(inp) for b, inp in zip(buffer, inputs[i])]
                    if self.valid_width > 1:
                        m.d.sync += buffer_valid.eq(self.si[i].valid)
            with m.Else():
                m.d.sync += bv.eq(0)
        
        for i, ifTransfer in enumerate(ifGen(m, (self.si[i].ready & ivalid[i] & ~used[i] for i in range(2)), withElse=False, startFromIf=False)):
            with ifTransfer:
                m.d.sync += [ovalid[1].eq(1)] + [
                    o.eq(inp) for o, inp in zip(outputs[1], inputs[i])
                ]
                if self.valid_width > 1:
                    m.d.sync += self.so.valid.eq(self.si[i].valid)
                with m.If(self.si[not i].ready & ivalid[not i] & ~used[not i] ):
                    m.d.sync += [
                        bv.eq(1),
                        rr_prio.eq(Mux(ivalid[i], i, not i))
                    ] + [b.eq(inp) for b, inp in zip(buffer, inputs[not i])]
                    if self.valid_width > 1:
                        m.d.sync += buffer_valid.eq(self.si[not i].valid)
        
        with m.Elif(self.so[1].ready):
            m.d.sync += self.so[1].valid.eq(0)

        return m


class StreamDistribute_1to2(Elaboratable):

    def __init__(self, T=StreamInterface, payload_width=8, valid_width=1, max_width=256, optimized_valid_in=False, optimized_valid_out=False, zero_payload_at_nv=False, extra_fields=[]):
        assert(T in [StreamInterface, BasicStreamInterface, ArrayStreamInterface])

        self.max_width = max_width
        self.optimized_valid_in = optimized_valid_in
        self.optimized_valid_out = optimized_valid_out
        self.si = T(name=f"si", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_in else [])+extra_fields)
        self.so = [T(name=f"so{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if self.optimized_valid_out else [])+extra_fields) for i in range(2)]
        self.payload_width = payload_width
        self.valid_width = valid_width

        self.zero_payload_at_nv = zero_payload_at_nv
        self.fixed_prio=True


    def ports(self):
        return sum([[s[f] for f in s.fields] for s in [self.si] + self.so], [])

    def elaborate(self, platform):

        m = Module()

        data_in = [field for field in self.si.fields if field not in ["ready"]]
        data_out = [[field for field in so.fields if field not in ["ready"]] for so in self.so]

        if m.setPureIdentifier(type(self), type(self.si), tuple(self.si._extra_fields), self.max_width, self.payload_width, self.valid_width, self.optimized_valid_in, self.optimized_valid_out, self.zero_payload_at_nv):
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"),
            o_si0_ready=self.si.ready,
            i_so0_ready=self.so[0].ready, i_so1_ready=self.so[1].ready,
            **{f"i_si_{f}":self.si[f] for f in data_in},
            **{f"o_so0_{f}":self.so[0][f] for f in data_out[0]},
            **{f"o_so1_{f}":self.so[1][f] for f in data_out[1]}
            )
            return m
        
        print("Elaborating ", self.__class__.__name__, self)
        
        for so in self.so:
            for field in so.fields:
                if field not in ["valid", "ready"]:
                    so[field].reset_less = True

        if self.optimized_valid_in:
            ivalid = self.si.o_valid
            ovalid = [Signal(name=f"ovalid{i}") for i in range(2)]
        elif self.valid_width == 1:
            ivalid = self.si.valid
            ovalid = [self.so[i].valid for i in range(2)]
        else:
            ivalid = Signal(name=f"ivalid")
            m.d.comb += ivalid.eq(self.si.valid.any())
            ovalid = [Signal(name=f"ovalid{i}") for i in range(2)]
        
        active_ovalid = self.optimized_valid_in or (self.valid_width > 1)

        if self.optimized_valid_out:
            m.d.comb += [self.so[i].o_valid.eq(ovalid[i]) for i in range(2)]

        outputs0 = []
        outputs1 = []
        inputs = []

        for f in self.si.fields:
            
            if f in ["valid", "ready", "o_valid"]:
                continue

            assert f in self.so[0].fields
            assert f in self.so[1].fields
            
            f_len = len(self.si[f])
            if (self.max_width < 1) or (f_len <= self.max_width):
                inputs.append(self.si[f])
                outputs0.append(self.so[0][f])
                outputs1.append(self.so[1][f])
                continue
            indexes = []
            ind = 0
            while ind < f_len:
                indexes.append(ind)
                ind += self.max_width
            indexes.append(ind)
            for i in range(len(indexes)-1):
                i0 = indexes[i]
                i1 = indexes[i+1]
                o0 = Signal(i1-i0, name=f"output0_{f}{i}")
                m.d.comb += self.so[0][f][i0:i1].eq(o0)
                outputs0.append(o0)
                o1 = Signal(i1-i0, name=f"output1_{f}{i}")
                m.d.comb += self.so[1][f][i0:i1].eq(o1)
                outputs1.append(o1)
                input_S = Signal(i1-i0, name=f"input_{f}{i}")
                m.d.comb += input_S.eq(self.si[f][i0:i1])
                inputs.append(input_S)
            
        ready0 = Signal()
        m.d.comb += ready0.eq(self.so[0].ready | ~(ovalid[0]))
        ready1 = Signal()
        m.d.comb += ready1.eq(self.so[1].ready | ~(ovalid[1]))

        with m.If(ready0 & ivalid):
                m.d.sync += [self.so[0].valid.eq(self.si.valid)]  + [outputs0[i].eq(inputs[i]) for i in range(len(inputs))]
                if active_ovalid:
                    m.d.sync += ovalid[0].eq(1)
        with m.Elif(self.so[0].ready):
            m.d.sync += self.so[0].valid.eq(0)
            if active_ovalid:
                m.d.sync += ovalid[0].eq(0)
            if self.zero_payload_at_nv:
                m.d.sync += [outputs0[i].eq(0) for i in range(len(outputs0))]
        with m.If(ivalid & ready1 & ~ready0):
            m.d.sync += [self.so[1].valid.eq(self.si.valid)] + [outputs1[i].eq(inputs[i]) for i in range(len(inputs))]
            if active_ovalid:
                m.d.sync += ovalid[1].eq(1)
        with m.Elif(self.so[1].ready):
            m.d.sync += self.so[1].valid.eq(0)
            if active_ovalid:
                m.d.sync += ovalid[1].eq(0)
            if self.zero_payload_at_nv:
                m.d.sync += [outputs1[i].eq(0) for i in range(len(outputs1))]
        
        m.d.comb += self.si.ready.eq(ready1 | ready0)

        return m

class RegTest(FHDLTestCase):
    def test_formal(self):
        self.assertFormal(StreamReg(T=BasicStreamInterface, payload_width=8, valid_width=1), mode="prove", depth=25)
        self.assertFormal(StreamReg(T=BasicStreamInterface, payload_width=8, valid_width=1, use_double_buffering=False), mode="prove", depth=25)
        self.assertFormal(StreamReg(T=BasicStreamInterface, payload_width=8, valid_width=4), mode="prove", depth=25)