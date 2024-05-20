from amaranth import *
from amlib.stream import StreamInterface
from amaranth.tracer import get_var_name

class AXI4_A_Interface(StreamInterface, Record):
    def __init__(self, *, name=None, addr_width=64, id_width=1, user_width=0, src_loc_at=0):

        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self._userField = ['user'] if user_width>0 else []
        user = [(u, user_width) for u in self._userField]

        # ... and create our basic stream.
        Record.__init__(self,[
            ('valid', 1),
            ('ready', 1),
            ('addr', addr_width),
            ('id', id_width),
            ('len', 8),
            ('size', 3),
            ('burst', 2),
            ('lock', 2),
            ('cache', 4),
            ('prot', 3),
            ('qos', 4),
            ('region', 4),
            *user
        ], name=new_name)
    
    def attach(self, interface, omit=None):
        # Create lists of fields to be copied -to- the interface (RHS fields),
        # and lists of fields to be copied -from- the interface (LHS fields).
        rhs_fields = ['valid','addr','id','len','size','burst','lock','cache','prot','qos','region',*self._userField]
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

class AXI4_W_Interface(StreamInterface, Record):
    def __init__(self, *, name=None, data_width=64, id_width=1, user_width=0, src_loc_at=0):

        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self._userField = ['user'] if user_width>0 else []
        user = [(u, user_width) for u in self._userField]

        # ... and create our basic stream.
        Record.__init__(self,[
            ('valid', 1),
            ('ready', 1),
            ('data', data_width),
            ('strb', data_width//8),
            ('last', 1),
            ('id', id_width),
            *user
        ], name=new_name)
    
    def attach(self, interface, omit=None):
        # Create lists of fields to be copied -to- the interface (RHS fields),
        # and lists of fields to be copied -from- the interface (LHS fields).
        rhs_fields = ['valid','data','strb','last','id',*self._userField]
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

class AXI4_B_Interface(StreamInterface, Record):
    def __init__(self, *, name=None, id_width=1, user_width=0, src_loc_at=0):

        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self._userField = ['user'] if user_width>0 else []
        user = [(u, user_width) for u in self._userField]

        # ... and create our basic stream.
        Record.__init__(self,[
            ('valid', 1),
            ('ready', 1),
            ('resp', 2),
            ('id', id_width),
            *user
        ], name=new_name)
    
    def attach(self, interface, omit=None):
        # Create lists of fields to be copied -to- the interface (RHS fields),
        # and lists of fields to be copied -from- the interface (LHS fields).
        rhs_fields = ['valid','resp','id',*self._userField]
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

class AXI4_R_Interface(StreamInterface, Record):
    def __init__(self, *, name=None, data_width=64, id_width=1, user_width=0, src_loc_at=0):

        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self._userField = ['user'] if user_width>0 else []
        user = [(u, user_width) for u in self._userField]

        # ... and create our basic stream.
        Record.__init__(self,[
            ('valid', 1),
            ('ready', 1),
            ('data', data_width),
            ('last', 1),
            ('resp', 2),
            ('id', id_width),
            *user
        ], name=new_name)
    
    def attach(self, interface, omit=None):
        # Create lists of fields to be copied -to- the interface (RHS fields),
        # and lists of fields to be copied -from- the interface (LHS fields).
        rhs_fields = ['valid','data','last','resp','id',*self._userField]
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


class AXI4_Read_Channels(StreamInterface):
    def __init__(self, *, name=None, addr_width=64, data_width=64, id_width=1, user_width=0, src_loc_at=0):
        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self.ar_channel = AXI4_A_Interface(name=new_name+"_ar", addr_width=addr_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.r_channel  = AXI4_R_Interface(name=new_name+"_r", data_width=data_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)

        self._ar_fields = self.ar_channel.fields.keys()
        self._r_fields = self.r_channel.fields.keys()

    def attach(self, interface, omit=None):
        assignments = []

        if omit == None:
            omit = []
        
        if "ar_channel" not in omit:
            ar_omit = list(filter(lambda f: (f in self._ar_fields) or (f[:2]=="ar" and f[2:] in self._ar_fields), omit))
            assignments += self.ar_channel.attach(interface.ar_channel, omit=ar_omit)
        
        if "r_channel" not in omit:
            r_omit = list(filter(lambda f: (f in self._r_fields) or (f[:1]=="r" and f[1:] in self._r_fields), omit))
            assignments += interface.r_channel.attach(self.r_channel, omit=r_omit)

        return assignments
    
    def __getattr__(self, attr):
        if attr[:2]=="ar" and attr[2:] in self._ar_fields:
            return self.ar_channel[attr[2:]]
        elif attr[:1]=="r" and attr[1:] in self._r_fields:
            return self.r_channel[attr[1:]]
        else:
            raise AttributeError(f"{attr} not in {type(self)}", obj=self)

    def __repr__(self):
        return f'''AR:{self.ar_channel.__repr__()}
R:{self.r_channel.__repr__()}'''

class AXI4_Write_Channels(StreamInterface):
    def __init__(self, *, name=None, addr_width=64, data_width=64, id_width=1, user_width=0, src_loc_at=0):
        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self.aw_channel = AXI4_A_Interface(name=new_name+"_aw", addr_width=addr_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.w_channel  = AXI4_R_Interface(name=new_name+"_w", data_width=data_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.b_channel  = AXI4_B_Interface(name=new_name+"_b", id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)

        self._aw_fields = self.aw_channel.fields.keys()
        self._w_fields = self.w_channel.fields.keys()
        self._b_fields = self.b_channel.fields.keys()

    def attach(self, interface, omit=None):
        assignments = []

        if omit == None:
            omit = []
        
        if "aw_channel" not in omit:
            aw_omit = list(filter(lambda f: (f in self._aw_fields) or (f[:2]=="aw" and f[2:] in self._aw_fields), omit))
            assignments += self.aw_channel.attach(interface.aw_channel, omit=aw_omit)
        
        if "w_channel" not in omit:
            w_omit = list(filter(lambda f: (f in self._w_fields) or (f[:1]=="w" and f[1:] in self._w_fields), omit))
            assignments += self.w_channel.attach(interface.w_channel, omit=w_omit)
        
        if "b_channel" not in omit:
            b_omit = list(filter(lambda f: (f in self._b_fields) or (f[:1]=="b" and f[1:] in self._b_fields), omit))
            assignments += interface.b_channel.attach(self.b_channel, omit=b_omit)

        return assignments
    
    def __getattr__(self, attr):
        if attr[:2]=="aw" and attr[2:] in self._aw_fields:
            return self.aw_channel[attr[2:]]
        elif attr[:1]=="w" and attr[1:] in self._w_fields:
            return self.w_channel[attr[1:]]
        elif attr[:1]=="b" and attr[1:] in self._b_fields:
            return self.b_channel[attr[1:]]
        else:
            raise AttributeError(f"{attr} not in {type(self)}", obj=self)

    def __repr__(self):
            return f'''AW:{self.aw_channel.__repr__()}
W:{self.w_channel.__repr__()}
B:{self.b_channel.__repr__()}'''

class AXI4_ReadWrite_Channels(StreamInterface):
    def __init__(self, *, name=None, addr_width=64, data_width=64, id_width=1, user_width=0, src_loc_at=0):
        new_name = name or get_var_name(depth=2 + src_loc_at, default=None)

        self.ar_channel = AXI4_A_Interface(name=new_name+"_ar", addr_width=addr_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.r_channel  = AXI4_R_Interface(name=new_name+"_r", data_width=data_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.aw_channel = AXI4_A_Interface(name=new_name+"_aw", addr_width=addr_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.w_channel  = AXI4_W_Interface(name=new_name+"_w", data_width=data_width, id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)
        self.b_channel  = AXI4_B_Interface(name=new_name+"_b", id_width=id_width, user_width=user_width, src_loc_at=src_loc_at+1)

        self._ar_fields = self.ar_channel.fields.keys()
        self._r_fields = self.r_channel.fields.keys()
        self._aw_fields = self.aw_channel.fields.keys()
        self._w_fields = self.w_channel.fields.keys()
        self._b_fields = self.b_channel.fields.keys()

    def attach(self, interface, omit=None):
        assignments = []

        if omit == None:
            omit = []

        if "ar_channel" not in omit and hasattr(interface, "ar_channel"):
            ar_omit = list(filter(lambda f: (f in self._ar_fields) or (f[:2]=="ar" and f[2:] in self._ar_fields), omit))
            assignments += self.ar_channel.attach(interface.ar_channel, omit=ar_omit)
        
        if "r_channel" not in omit and hasattr(interface, "r_channel"):
            r_omit = list(filter(lambda f: (f in self._r_fields) or (f[:1]=="r" and f[1:] in self._r_fields), omit))
            assignments += interface.r_channel.attach(self.r_channel, omit=r_omit)
        
        if "aw_channel" not in omit and hasattr(interface, "aw_channel"):
            aw_omit = list(filter(lambda f: (f in self._aw_fields) or (f[:2]=="aw" and f[2:] in self._aw_fields), omit))
            assignments += self.aw_channel.attach(interface.aw_channel, omit=aw_omit)
        
        if "w_channel" not in omit and hasattr(interface, "w_channel"):
            w_omit = list(filter(lambda f: (f in self._w_fields) or (f[:1]=="w" and f[1:] in self._w_fields), omit))
            assignments += self.w_channel.attach(interface.w_channel, omit=w_omit)
        
        if "b_channel" not in omit and hasattr(interface, "b_channel"):
            b_omit = list(filter(lambda f: (f in self._b_fields) or (f[:1]=="b" and f[1:] in self._b_fields), omit))
            assignments += interface.b_channel.attach(self.b_channel, omit=b_omit)

        return assignments
    
    def __getattr__(self, attr):
        if attr[:2]=="ar" and attr[2:] in self._ar_fields:
            return self.ar_channel[attr[2:]]
        elif attr[:1]=="r" and attr[1:] in self._r_fields:
            return self.r_channel[attr[1:]]
        elif attr[:2]=="aw" and attr[2:] in self._aw_fields:
            return self.aw_channel[attr[2:]]
        elif attr[:1]=="w" and attr[1:] in self._w_fields:
            return self.w_channel[attr[1:]]
        elif attr[:1]=="b" and attr[1:] in self._b_fields:
            return self.b_channel[attr[1:]]
        else:
            raise AttributeError(f"{attr} not in {type(self)}", obj=self)
    
    def __repr__(self):
        return f'''AR:{self.ar_channel.__repr__()}
R:{self.r_channel.__repr__()}
AW:{self.aw_channel.__repr__()}
W:{self.w_channel.__repr__()}
B:{self.b_channel.__repr__()}'''