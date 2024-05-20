
from amaranth import *
from amaranth.asserts import Assert, Assume, Cover
from amaranth.sim import Simulator, Delay, Settle
from fhdl import FHDLTestCase
import operator
from functools import reduce
from typing import Callable, Tuple, Hashable
from collections import OrderedDict
from utils import cl2

from Stream import StreamReg, ArrayStreamInterface, BasicStreamInterface, StreamDistribute_2to2, StreamJoin
from amaranth.lib.data import *

# sorting network designs with least number of layers from https://bertdobbelaere.github.io/sorting_networks.html
# for inputs 17 and fewer, the depth is optimal
perfectSortings = {
           2: [[(0,1)]],
           3: [[(0,2)], [(0,1)], [(1,2)]],
           4: [[(0,2),(1,3)], [(0,1),(2,3)], [(1,2)]],
           5: [[(0,3),(1,4)], [(0,2),(1,3)], [(0,1),(2,4)], [(1,2),(3,4)], [(2,3)]],
           6: [[(0,5),(1,3),(2,4)], [(1,2),(3,4)], [(0,3),(2,5)], [(0,1),(2,3),(4,5)], [(1,2),(3,4)]],
           7: [[(0,6),(2,3),(4,5)], [(0,2),(1,4),(3,6)], [(0,1),(2,5),(3,4)], [(1,2),(4,6)], [(2,3),(4,5)], [(1,2),(3,4),(5,6)]],
           8: [[(0,2),(1,3),(4,6),(5,7)], [(0,4),(1,5),(2,6),(3,7)], [(0,1),(2,3),(4,5),(6,7)], [(2,4),(3,5)], [(1,4),(3,6)], [(1,2),(3,4),(5,6)]],
           9: [[(0,3),(1,7),(2,5),(4,8)], [(0,7),(2,4),(3,8),(5,6)], [(0,2),(1,3),(4,5),(7,8)], [(1,4),(3,6),(5,7)], [(0,1),(2,4),(3,5),(6,8)], [(2,3),(4,5),(6,7)], [(1,2),(3,4),(5,6)]],
           10: [[(0,1),(2,5),(3,6),(4,7),(8,9)], [(0,6),(1,8),(2,4),(3,9),(5,7)], [(0,2),(1,3),(4,5),(6,8),(7,9)], [(0,1),(2,7),(3,5),(4,6),(8,9)], [(1,2),(3,4),(5,6),(7,8)], [(1,3),(2,4),(5,7),(6,8)], [(2,3),(4,5),(6,7)]],
           11: [[(0,9),(1,6),(2,4),(3,7),(5,8)], [(0,1),(3,5),(4,10),(6,9),(7,8)], [(1,3),(2,5),(4,7),(8,10)], [(0,4),(1,2),(3,7),(5,9),(6,8)], [(0,1),(2,6),(4,5),(7,8),(9,10)], [(2,4),(3,6),(5,7),(8,9)], [(1,2),(3,4),(5,6),(7,8)], [(2,3),(4,5),(6,7)]],
           12: [[(0,8),(1,7),(2,6),(3,11),(4,10),(5,9)], [(0,2),(1,4),(3,5),(6,8),(7,10),(9,11)], [(0,1),(2,9),(4,7),(5,6),(10,11)], [(1,3),(2,7),(4,9),(8,10)], [(0,1),(2,3),(4,5),(6,7),(8,9),(10,11)], [(1,2),(3,5),(6,8),(9,10)], [(2,4),(3,6),(5,8),(7,9)], [(1,2),(3,4),(5,6),(7,8),(9,10)]],
           13: [[(0,11),(1,7),(2,4),(3,5),(8,9),(10,12)], [(0,2),(3,6),(4,12),(5,7),(8,10)], [(0,8),(1,3),(2,5),(4,9),(6,11),(7,12)], [(0,1),(2,10),(3,8),(4,6),(9,11)], [(1,3),(2,4),(5,10),(6,8),(7,9),(11,12)], [(1,2),(3,4),(5,8),(6,9),(7,10)], [(2,3),(4,7),(5,6),(8,11),(9,10)], [(4,5),(6,7),(8,9),(10,11)], [(3,4),(5,6),(7,8),(9,10)]],
           14: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)], [(0,2),(1,3),(4,8),(5,9),(10,12),(11,13)], [(0,10),(1,6),(2,11),(3,13),(5,8),(7,12)], [(1,4),(2,8),(3,6),(5,11),(7,10),(9,12)], [(0,1),(3,9),(4,10),(5,7),(6,8),(12,13)], [(1,5),(2,4),(3,7),(6,10),(8,12),(9,11)], [(1,2),(3,5),(4,6),(7,9),(8,10),(11,12)], [(2,3),(4,5),(6,7),(8,9),(10,11)], [(3,4),(5,6),(7,8),(9,10)]],
           15: [[(0,6),(1,10),(2,14),(3,9),(4,12),(5,13),(7,11)], [(0,7),(2,5),(3,4),(6,11),(8,10),(9,12),(13,14)], [(1,13),(2,3),(4,6),(5,9),(7,8),(10,14),(11,12)], [(0,3),(1,4),(5,7),(6,13),(8,9),(10,11),(12,14)], [(0,2),(1,5),(3,8),(4,6),(7,10),(9,11),(12,13)], [(0,1),(2,5),(3,10),(4,8),(6,7),(9,12),(11,13)], [(1,2),(3,4),(5,6),(7,9),(8,10),(11,12)], [(3,5),(4,6),(7,8),(9,10)], [(2,3),(4,5),(6,7),(8,9),(10,11)]],
           16: [[(0,5),(1,4),(2,12),(3,13),(6,7),(8,9),(10,15),(11,14)], [(0,2),(1,10),(3,6),(4,7),(5,14),(8,11),(9,12),(13,15)], [(0,8),(1,3),(2,11),(4,13),(5,9),(6,10),(7,15),(12,14)], [(0,1),(2,4),(3,8),(5,6),(7,12),(9,10),(11,13),(14,15)], [(1,3),(2,5),(4,8),(6,9),(7,11),(10,13),(12,14)], [(1,2),(3,5),(4,11),(6,8),(7,9),(10,12),(13,14)], [(2,3),(4,5),(6,7),(8,9),(10,11),(12,13)], [(4,6),(5,7),(8,10),(9,11)], [(3,4),(5,6),(7,8),(9,10),(11,12)]],
           17: [[(1,2),(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)], [(1,3),(2,4),(5,7),(6,8),(9,11),(10,12),(13,15),(14,16)], [(1,5),(2,6),(3,7),(4,8),(9,13),(10,14),(11,15),(12,16)], [(0,3),(1,13),(2,10),(4,7),(5,11),(6,12),(8,9),(14,15)], [(0,13),(1,8),(2,5),(3,6),(4,14),(7,15),(9,16),(10,11)], [(0,1),(2,8),(3,4),(5,10),(6,13),(7,11),(12,14)], [(1,5),(3,8),(4,10),(6,7),(9,12),(11,13)], [(1,2),(4,6),(5,8),(7,10),(9,11),(12,14),(13,15)], [(2,3),(4,5),(6,8),(7,9),(10,11),(12,13),(14,15)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)]],
           18: [[(0,6),(1,10),(2,15),(3,5),(4,9),(7,16),(8,13),(11,17),(12,14)], [(0,12),(1,4),(3,11),(5,17),(6,14),(7,8),(9,10),(13,16)], [(1,13),(2,7),(4,16),(6,9),(8,11),(10,15)], [(0,1),(2,3),(4,12),(5,13),(7,9),(8,10),(14,15),(16,17)], [(0,2),(1,11),(3,4),(5,7),(6,16),(10,12),(13,14),(15,17)], [(1,8),(4,10),(5,6),(7,13),(9,16),(11,12)], [(1,3),(2,5),(4,7),(6,8),(9,11),(10,13),(12,15),(14,16)], [(1,2),(3,5),(4,6),(7,9),(8,10),(11,13),(12,14),(15,16)], [(2,3),(5,8),(6,7),(9,12),(10,11),(14,15)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14)], [(4,5),(6,7),(8,9),(10,11),(12,13)]],
           19: [[(0,1),(2,3),(4,5),(6,7),(8,10),(11,12),(13,14),(15,16),(17,18)], [(0,2),(1,3),(4,6),(5,7),(8,9),(11,13),(12,14),(15,17),(16,18)], [(0,4),(1,5),(2,6),(3,7),(9,10),(11,15),(12,16),(13,17),(14,18)], [(0,11),(1,8),(2,13),(3,17),(4,10),(5,6),(9,16),(12,15)], [(1,2),(3,13),(4,12),(5,14),(6,16),(7,10),(8,15)], [(0,1),(2,11),(3,9),(5,12),(6,15),(7,13),(10,18),(14,17)], [(1,4),(3,8),(5,11),(6,9),(7,12),(10,13),(14,15),(16,17)], [(2,4),(3,5),(6,7),(8,11),(9,12),(10,14),(13,15)], [(2,3),(4,5),(6,8),(7,9),(10,11),(12,14),(13,16),(15,17)], [(1,2),(4,6),(5,8),(7,10),(9,11),(12,13),(14,16)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)]],
           20: [[(0,12),(1,13),(2,14),(3,15),(4,16),(5,17),(6,18),(7,19),(8,10),(9,11)], [(0,2),(1,3),(4,6),(5,7),(8,9),(10,11),(12,14),(13,15),(16,18),(17,19)], [(0,1),(2,3),(4,5),(6,7),(12,13),(14,15),(16,17),(18,19)], [(0,4),(1,12),(2,16),(3,17),(5,8),(6,9),(7,18),(10,13),(11,14),(15,19)], [(1,6),(3,10),(4,5),(7,11),(8,12),(9,16),(13,18),(14,15)], [(0,4),(2,8),(3,9),(6,7),(10,16),(11,17),(12,13),(15,19)], [(1,4),(3,6),(5,8),(7,10),(9,12),(11,14),(13,16),(15,18)], [(2,3),(4,5),(6,8),(7,9),(10,12),(11,13),(14,15),(16,17)], [(2,4),(3,6),(5,7),(8,10),(9,11),(12,14),(13,16),(15,17)], [(1,2),(3,5),(6,7),(8,9),(10,11),(12,13),(14,16),(17,18)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)]],
           21: [[(0,7),(1,10),(3,5),(4,8),(6,13),(9,19),(11,14),(12,17),(15,16),(18,20)], [(0,11),(1,15),(2,12),(3,4),(5,8),(6,9),(7,14),(10,16),(13,19),(17,20)], [(0,6),(1,3),(2,18),(4,15),(5,10),(8,16),(11,17),(12,13),(14,20)], [(2,6),(5,12),(7,18),(8,14),(9,11),(10,17),(13,19),(16,20)], [(1,2),(4,7),(5,9),(6,17),(10,13),(11,12),(14,19),(15,18)], [(0,2),(3,6),(4,5),(7,10),(8,11),(9,15),(12,16),(13,18),(14,17),(19,20)], [(0,1),(2,3),(5,9),(6,12),(7,8),(11,14),(13,15),(16,19),(17,18)], [(1,2),(3,9),(6,13),(10,11),(12,15),(16,17),(18,19)], [(1,4),(2,5),(3,7),(6,10),(8,9),(11,12),(13,14),(17,18)], [(2,4),(5,6),(7,8),(9,11),(10,13),(12,15),(14,16)], [(3,4),(5,7),(6,8),(9,10),(11,13),(12,14),(15,16)], [(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17)]],
           22: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21)], [(0,2),(1,3),(4,6),(5,7),(8,10),(11,13),(14,16),(15,17),(18,20),(19,21)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(14,18),(15,19),(16,20),(17,21)], [(0,14),(1,15),(2,18),(3,19),(4,16),(5,17),(6,20),(7,21),(9,11),(10,12)], [(0,8),(2,10),(4,14),(5,12),(6,15),(7,17),(9,16),(11,19),(13,21)], [(1,9),(2,4),(3,16),(5,18),(6,10),(7,13),(8,14),(11,15),(12,20),(17,19)], [(1,8),(3,11),(4,5),(7,12),(9,14),(10,18),(13,20),(16,17)], [(1,2),(3,5),(4,8),(6,9),(7,11),(10,14),(12,15),(13,17),(16,18),(19,20)], [(2,4),(3,6),(5,9),(7,10),(11,14),(12,16),(15,18),(17,19)], [(3,4),(5,7),(6,8),(9,11),(10,12),(13,15),(14,16),(17,18)], [(5,6),(7,8),(9,10),(11,12),(13,14),(15,16)], [(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17)]],
           23: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(17,19),(18,20),(21,22)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,21),(17,22)], [(1,10),(2,9),(3,11),(6,19),(12,17),(14,22),(16,18),(20,21)], [(0,16),(1,2),(3,21),(4,17),(5,14),(6,13),(7,22),(9,18),(10,20),(15,19)], [(1,10),(2,9),(3,17),(4,12),(5,18),(6,20),(7,15),(8,16),(11,14),(13,21),(19,22)], [(0,8),(1,4),(2,10),(3,9),(5,6),(11,21),(12,16),(13,20),(14,15),(17,18)], [(2,8),(3,5),(4,12),(6,9),(7,11),(10,16),(13,17),(15,21),(18,20)], [(1,2),(4,8),(5,10),(6,12),(7,13),(9,16),(11,18),(14,17),(15,19)], [(2,4),(3,5),(6,8),(7,9),(10,12),(11,13),(14,16),(15,20),(17,18),(19,21)], [(3,6),(5,8),(7,10),(9,12),(11,14),(13,16),(15,17),(18,20)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20)]],
           24: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(17,21),(18,22),(19,23)], [(0,16),(1,18),(2,17),(3,19),(4,20),(5,22),(6,21),(7,23),(9,10),(13,14)], [(2,10),(3,11),(5,18),(6,14),(7,15),(8,16),(9,17),(12,20),(13,21)], [(0,8),(1,9),(2,12),(3,20),(4,16),(5,13),(6,17),(7,19),(10,18),(11,21),(14,22),(15,23)], [(1,8),(3,16),(4,12),(5,10),(6,9),(7,20),(11,19),(13,18),(14,17),(15,22)], [(2,4),(3,5),(7,13),(9,12),(10,16),(11,14),(18,20),(19,21)], [(1,2),(4,8),(5,9),(6,10),(7,11),(12,16),(13,17),(14,18),(15,19),(21,22)], [(2,4),(3,8),(5,6),(7,9),(10,12),(11,13),(14,16),(15,20),(17,18),(19,21)], [(3,5),(6,8),(7,10),(9,12),(11,14),(13,16),(15,17),(18,20)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20)]],
           25: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,24)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(21,22),(23,24)], [(0,8),(1,12),(2,10),(3,14),(4,9),(5,13),(6,11),(7,15),(17,22),(18,21),(19,24)], [(1,18),(3,9),(5,17),(6,20),(7,13),(11,14),(12,22),(15,24),(21,23)], [(1,16),(3,12),(5,21),(6,18),(7,11),(10,17),(14,23),(19,20)], [(0,1),(2,5),(4,16),(6,8),(7,18),(9,21),(10,14),(11,13),(12,19),(15,23),(20,22)], [(1,2),(3,5),(4,6),(7,9),(8,12),(10,16),(11,20),(13,22),(14,17),(15,18),(19,21)], [(1,4),(2,6),(3,7),(5,9),(8,10),(11,14),(12,16),(13,17),(15,19),(18,20),(22,23)], [(2,4),(3,8),(5,10),(7,12),(9,16),(11,15),(13,19),(14,21),(17,18),(20,22)], [(3,4),(5,8),(6,7),(9,12),(10,11),(13,16),(14,15),(17,19),(18,21)], [(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(20,21)], [(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19)]],
           26: [[(0,25),(1,24),(2,23),(3,19),(4,21),(5,20),(6,22),(7,18),(8,16),(9,17),(10,15),(11,14),(12,13)], [(0,1),(2,5),(3,6),(4,8),(7,10),(9,16),(11,12),(13,14),(15,18),(17,21),(19,22),(20,23),(24,25)], [(0,17),(1,24),(2,11),(3,7),(4,9),(5,13),(6,15),(8,25),(10,19),(12,20),(14,23),(16,21),(18,22)], [(0,4),(1,9),(2,3),(5,6),(7,12),(8,17),(10,11),(13,18),(14,15),(16,24),(19,20),(21,25),(22,23)], [(0,7),(1,5),(3,4),(6,9),(8,10),(11,12),(13,14),(15,17),(16,19),(18,25),(20,24),(21,22)], [(0,2),(4,12),(5,20),(7,8),(10,14),(11,15),(13,21),(17,18),(23,25)], [(1,7),(2,3),(4,13),(5,10),(6,8),(9,14),(11,16),(12,21),(15,20),(17,19),(18,24),(22,23)], [(1,2),(3,7),(4,11),(5,6),(8,9),(10,13),(12,15),(14,21),(16,17),(18,22),(19,20),(23,24)], [(3,4),(6,11),(8,16),(9,17),(10,12),(13,15),(14,19),(21,22)], [(2,3),(4,5),(7,11),(8,10),(9,12),(13,16),(14,18),(15,17),(20,21),(22,23)], [(3,4),(5,8),(6,7),(9,10),(11,13),(12,14),(15,16),(17,20),(18,19),(21,22)], [(5,6),(7,8),(9,11),(10,13),(12,15),(14,16),(17,18),(19,20)], [(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21)]],
           27: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23),(24,26)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(17,21),(18,22),(19,23),(25,26)], [(0,8),(1,9),(2,10),(3,11),(4,12),(5,13),(6,14),(7,15),(16,24),(17,25),(20,26),(21,22)], [(0,16),(1,18),(2,24),(3,5),(4,20),(8,17),(10,26),(11,19),(22,25)], [(1,4),(2,8),(3,21),(5,9),(6,10),(11,12),(13,19),(14,26),(17,24),(18,20)], [(1,16),(3,11),(4,8),(6,17),(9,25),(10,24),(12,21),(14,22),(23,26)], [(1,2),(5,14),(7,23),(8,16),(9,18),(10,20),(11,17),(13,22),(15,26),(21,24)], [(2,4),(3,5),(6,9),(7,13),(10,16),(12,18),(14,20),(15,25),(17,21),(19,23),(22,24)], [(3,6),(4,8),(5,9),(7,12),(11,16),(13,18),(14,17),(15,19),(20,21),(23,25)], [(2,4),(5,10),(6,11),(7,14),(9,16),(12,20),(13,17),(15,22),(18,21),(19,24)], [(5,8),(7,11),(9,10),(12,13),(14,16),(15,20),(17,18),(19,21),(23,24)], [(3,5),(6,8),(7,9),(10,11),(12,14),(13,16),(15,17),(18,20),(19,22),(21,23)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22)]],
           28: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23),(24,26),(25,27)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(14,18),(15,19),(20,24),(21,25),(22,26),(23,27)], [(0,20),(1,21),(2,22),(3,23),(4,24),(5,25),(6,26),(7,27),(9,17),(10,18),(11,15),(12,16)], [(1,2),(4,20),(5,6),(7,23),(8,12),(9,16),(10,14),(11,18),(13,17),(15,19),(21,22),(25,26)], [(0,8),(1,9),(2,12),(3,5),(4,10),(6,16),(7,13),(11,21),(14,20),(15,25),(17,23),(18,26),(19,27),(22,24)], [(2,4),(3,7),(5,17),(8,14),(9,11),(10,22),(13,19),(16,18),(20,24),(23,25)], [(1,8),(3,9),(5,11),(6,10),(7,15),(12,20),(16,22),(17,21),(18,24),(19,26)], [(1,2),(4,6),(5,9),(10,16),(11,17),(12,14),(13,15),(18,22),(21,23),(25,26)], [(4,8),(6,12),(7,11),(10,14),(13,17),(15,21),(16,20),(19,23)], [(2,4),(6,8),(7,16),(9,14),(10,12),(11,20),(13,18),(15,17),(19,21),(23,25)], [(3,10),(5,12),(7,9),(11,13),(14,16),(15,22),(17,24),(18,20)], [(3,6),(5,8),(7,10),(9,12),(11,14),(13,16),(15,18),(17,20),(19,22),(21,24)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22),(23,24)]],
           29: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23),(24,26),(25,27)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(17,21),(18,22),(19,23),(24,28)], [(0,8),(1,9),(2,10),(3,11),(4,12),(5,13),(6,14),(7,15),(16,24),(17,25),(18,26),(19,27),(20,28)], [(0,16),(1,8),(2,4),(3,12),(5,10),(6,9),(7,14),(11,13),(17,24),(18,20),(19,28),(21,26),(22,25),(23,27)], [(1,2),(3,5),(4,8),(6,22),(7,11),(9,25),(10,12),(13,14),(17,18),(19,21),(20,24),(26,28)], [(1,17),(2,18),(3,19),(4,20),(5,10),(7,23),(8,24),(11,27),(12,28),(13,25),(21,26)], [(3,17),(4,16),(5,21),(6,18),(7,9),(8,20),(10,26),(11,23),(14,28),(15,27),(22,24)], [(1,4),(3,8),(5,16),(7,17),(9,21),(10,22),(11,19),(12,20),(14,24),(15,26),(23,28)], [(2,5),(7,8),(9,18),(11,17),(12,16),(13,22),(14,20),(15,19),(23,24)], [(2,4),(6,12),(9,16),(10,11),(13,17),(14,18),(15,22),(19,25),(20,21)], [(5,6),(8,12),(9,10),(11,13),(14,16),(15,17),(18,20),(19,23),(21,22),(25,26)], [(3,5),(6,7),(8,9),(10,12),(11,14),(13,16),(15,18),(17,20),(19,21),(22,23),(24,25),(26,28)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22),(23,24),(25,26),(27,28)]],
           30: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23),(24,26),(25,27)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(17,21),(18,22),(19,23),(24,28),(25,29)], [(0,8),(1,9),(2,10),(3,11),(4,12),(5,13),(6,14),(7,15),(16,24),(17,25),(18,26),(19,27),(20,28),(21,29)], [(0,16),(1,8),(2,4),(3,12),(5,10),(6,9),(7,14),(11,13),(17,24),(18,20),(19,28),(21,26),(22,25),(27,29)], [(1,2),(3,5),(4,8),(6,22),(7,11),(9,25),(10,12),(13,14),(17,18),(19,21),(20,24),(23,27),(26,28)], [(1,17),(2,18),(3,19),(4,20),(5,10),(7,23),(8,24),(11,27),(12,28),(13,29),(21,26)], [(3,17),(4,16),(5,21),(6,18),(7,9),(8,20),(10,26),(11,23),(13,25),(14,28),(15,27),(22,24)], [(1,4),(3,8),(5,16),(7,17),(9,21),(10,22),(11,19),(12,20),(14,24),(15,26),(23,28)], [(2,5),(7,8),(9,18),(11,17),(12,16),(13,22),(14,20),(15,19),(23,24),(26,29)], [(2,4),(6,12),(9,16),(10,11),(13,17),(14,18),(15,22),(19,25),(20,21),(27,29)], [(5,6),(8,12),(9,10),(11,13),(14,16),(15,17),(18,20),(19,23),(21,22),(25,26)], [(3,5),(6,7),(8,9),(10,12),(11,14),(13,16),(15,18),(17,20),(19,21),(22,23),(24,25),(26,28)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22),(23,24),(25,26),(27,28)]],
           31: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23),(24,26),(25,27),(28,30)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(17,21),(18,22),(19,23),(24,28),(25,29),(26,30)], [(0,8),(1,9),(2,10),(3,11),(4,12),(5,13),(6,14),(7,15),(16,24),(17,25),(18,26),(19,27),(20,28),(21,29),(22,30)], [(0,16),(1,8),(2,4),(3,12),(5,10),(6,9),(7,14),(11,13),(17,24),(18,20),(19,28),(21,26),(22,25),(23,30),(27,29)], [(1,2),(3,5),(4,8),(6,22),(7,11),(9,25),(10,12),(13,14),(17,18),(19,21),(20,24),(23,27),(26,28),(29,30)], [(1,17),(2,18),(3,19),(4,20),(5,10),(7,23),(8,24),(11,27),(12,28),(13,29),(14,30),(21,26)], [(3,17),(4,16),(5,21),(6,18),(7,9),(8,20),(10,26),(11,23),(13,25),(14,28),(15,27),(22,24)], [(1,4),(3,8),(5,16),(7,17),(9,21),(10,22),(11,19),(12,20),(14,24),(15,26),(23,28),(27,30)], [(2,5),(7,8),(9,18),(11,17),(12,16),(13,22),(14,20),(15,19),(23,24),(26,29)], [(2,4),(6,12),(9,16),(10,11),(13,17),(14,18),(15,22),(19,25),(20,21),(27,29)], [(5,6),(8,12),(9,10),(11,13),(14,16),(15,17),(18,20),(19,23),(21,22),(25,26)], [(3,5),(6,7),(8,9),(10,12),(11,14),(13,16),(15,18),(17,20),(19,21),(22,23),(24,25),(26,28)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22),(23,24),(25,26),(27,28)]],
           32: [[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)], [(0,2),(1,3),(4,6),(5,7),(8,10),(9,11),(12,14),(13,15),(16,18),(17,19),(20,22),(21,23),(24,26),(25,27),(28,30),(29,31)], [(0,4),(1,5),(2,6),(3,7),(8,12),(9,13),(10,14),(11,15),(16,20),(17,21),(18,22),(19,23),(24,28),(25,29),(26,30),(27,31)], [(0,8),(1,9),(2,10),(3,11),(4,12),(5,13),(6,14),(7,15),(16,24),(17,25),(18,26),(19,27),(20,28),(21,29),(22,30),(23,31)], [(0,16),(1,8),(2,4),(3,12),(5,10),(6,9),(7,14),(11,13),(15,31),(17,24),(18,20),(19,28),(21,26),(22,25),(23,30),(27,29)], [(1,2),(3,5),(4,8),(6,22),(7,11),(9,25),(10,12),(13,14),(17,18),(19,21),(20,24),(23,27),(26,28),(29,30)], [(1,17),(2,18),(3,19),(4,20),(5,10),(7,23),(8,24),(11,27),(12,28),(13,29),(14,30),(21,26)], [(3,17),(4,16),(5,21),(6,18),(7,9),(8,20),(10,26),(11,23),(13,25),(14,28),(15,27),(22,24)], [(1,4),(3,8),(5,16),(7,17),(9,21),(10,22),(11,19),(12,20),(14,24),(15,26),(23,28),(27,30)], [(2,5),(7,8),(9,18),(11,17),(12,16),(13,22),(14,20),(15,19),(23,24),(26,29)], [(2,4),(6,12),(9,16),(10,11),(13,17),(14,18),(15,22),(19,25),(20,21),(27,29)], [(5,6),(8,12),(9,10),(11,13),(14,16),(15,17),(18,20),(19,23),(21,22),(25,26)], [(3,5),(6,7),(8,9),(10,12),(11,14),(13,16),(15,18),(17,20),(19,21),(22,23),(24,25),(26,28)], [(3,4),(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(17,18),(19,20),(21,22),(23,24),(25,26),(27,28)]]
       }

def netDepth(width):

    def s(w):
        if w == 1:
            return 0
        elif w in perfectSortings:
            return len(perfectSortings[w])
        else:
            k = w//2
            w0 = k
            w1 = w - k
            return max(s(w0), s(w1)) + m(w)

    def m(w):
        if w == 1:
            return 0
        else:
            k = w//2
            w0 = k
            w1 = w - k
            return 1 + max(m(w0), m(w1))
    
    return s(width if (width in perfectSortings) else (1 << cl2(width)))

class SortingNet(Elaboratable):
    def __init__(self, comp:Callable[[Value, Value], Value], payload_width : int = 8, N : int = 8, registerStride=2, db_stride=1, endOnReg=True, useOptimal=True):
        self.payload_width = payload_width
        self.comp = comp
        self.N = N
        self.registerStride = registerStride # >= 0 for addition of registers
        self.db_stride = db_stride
        self.delay = 0 #Will be updated with the number of register levels added
        self.endOnReg = endOnReg
        self.useOptimal = useOptimal

        self.input_stream = ArrayStreamInterface(payload_width=self.payload_width, valid_width=self.N)
        self.output_stream = ArrayStreamInterface(payload_width=self.payload_width, valid_width=self.N)
    
    def ports(self, select=0):
        deRecord = lambda r: [r[f] for f in r.fields]
        if select==0:
            return deRecord(self.input_stream) + deRecord(self.output_stream)
        if select==1:
            return deRecord(self.input_stream)
        if select==2:
            return deRecord(self.output_stream)

    def elaborate(self, platform):

        m = Module()

        if m.setPureIdentifier(type(self), self.payload_width, self.comp, self.N, self.useOptimal, self.registerStride, self.endOnReg, self.db_stride):
            inputs = {f"{'o'if signal.name=='ready' else 'i'}_{signal.name}":signal for signal in self.ports(1)}
            outputs = {f"{'i'if signal.name=='ready' else 'o'}_{signal.name}":signal for signal in self.ports(2)}
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"), **inputs, **outputs)
            return m
        
        print("Elaborating ", self.__class__.__name__, self)

        regLayers = OrderedDict()

        swap_cnt = [0,0]

        def swap2(T0, T1, d):
            
            nonlocal swap_cnt

            T0v, T0p = T0
            T1v, T1p = T1

            payload0_i = Signal(len(T0p))
            valid0_i = Signal()
            payload1_i = Signal(len(T1p))
            valid1_i = Signal()

            m.d.comb += [
                valid0_i.eq(T0v),
                payload0_i.eq(T0p),
                valid1_i.eq(T1v),
                payload1_i.eq(T1p)
            ]

            payload0_o = Signal(len(T0p))
            valid0_o = Signal()
            payload1_o = Signal(len(T1p))
            valid1_o = Signal()

            sm = Module()
            m.submodules[f"swap_{['up','down'][d]}_{swap_cnt[d]}"] = sm
            swap_cnt[d] += 1
            if sm.setPureIdentifier(type(self), m._generated["p_signature"], len(T0p), d):
                sm.submodules += Instance("dummy",
                    i_payload0_i = payload0_i,
                    i_valid0_i = valid0_i,
                    i_payload1_i = payload1_i,
                    i_valid1_i = valid1_i,
                    o_payload0_o = payload0_o,
                    o_valid0_o = valid0_o,
                    o_payload1_o = payload1_o,
                    o_valid1_o = valid1_o
                )
                return ((valid0_o, payload0_o), (valid1_o, payload1_o))


            swap = Signal()

            sm.d.comb += swap.eq(((self.comp(payload0_i, payload1_i) == Const(d, 1)) & valid1_i & valid0_i) | ((valid1_i & ~valid0_i) if d else (valid0_i & ~valid1_i)))

            with sm.If(swap):
                sm.d.comb += [
                    valid0_o.eq(valid1_i),
                    payload0_o.eq(payload1_i),
                    valid1_o.eq(valid0_i),
                    payload1_o.eq(payload0_i)
                ]
            with sm.Else():
                sm.d.comb += [
                    valid0_o.eq(valid0_i),
                    payload0_o.eq(payload0_i),
                    valid1_o.eq(valid1_i),
                    payload1_o.eq(payload1_i)
                ]

            return ((valid0_o, payload0_o), (valid1_o, payload1_o))
        
        def bSort(A, d, level=0):
            cnt = len(A)
            if cnt <= 1:
                return A, level
            elif self.useOptimal and (cnt in perfectSortings.keys()):
                sorter = perfectSortings[cnt]
                for layer in sorter:
                    for swap in layer:
                        i0, i1 = swap
                        A[i0], A[i1] = swap2(A[i0], A[i1], d)
                    level += 1
                    if self.registerStride > 0 and (level%self.registerStride) == (self.registerStride-1):
                        B = [(Signal(), Signal(len(A[i][1]))) for i in range(cnt)]

                        s = regLayers.get(level,None)
                        v_b, e_b = zip(*B)
                        v_a, e_a = zip(*A)

                        if s == None:
                            regLayers[level] = e_a, v_a, e_b, v_b
                        else:
                            aE, aV, bE, bV = s
                            regLayers[level] = aE+e_a, aV+v_a, bE+e_b, bV+v_b

                        A = B
                
                return A, level
            else:
                k = cnt//2
                L, lev_l = bSort(A[:k], 1, level=level)
                R, lev_r = bSort(A[k:], 0, level=level)
                return bMerge(L+R, d, level=max(lev_l, lev_r))
            

    
        def bMerge(A, d, level=0):
            cnt = len(A)
            if cnt > 1:
                k = cnt//2
                B = [(Signal(), Signal(len(A[i][1]))) for i in range(cnt)]

                for i in range(0, k):
                    B[i], B[i+k] = swap2(A[i], A[i+k], d)
                level += 1

                if self.registerStride > 0 and (level%self.registerStride) == (self.registerStride-1):
                    C = [(Signal(), Signal(len(B[i][1]))) for i in range(cnt)]
                    s = regLayers.get(level,None)
                    v_b, e_b = zip(*C)
                    v_a, e_a = zip(*B)

                    if s == None:
                        regLayers[level] = e_a, v_a, e_b, v_b
                    else:
                        aE, aV, bE, bV = s
                        regLayers[level] = aE+e_a, aV+v_a, bE+e_b, bV+v_b
                    B = C
                
                L, lev_l = bMerge(B[:k], d, level=level)
                R, lev_r = bMerge(B[k:], d, level=level)


                return L+R, max(lev_l, lev_r)
            return A, level

        O, l = bSort([(self.input_stream.valid[i] & self.input_stream.ready, self.input_stream.payload[i]) for i in range(len(self.input_stream.valid))], 1)

        if self.endOnReg and (l not in regLayers):
            B = [(Signal(), Signal(len(O[i][1]))) for i in range(len(O))]
            v_b, e_b = zip(*B)
            v_a, e_a = zip(*O)
            regLayers[l] = e_a, v_a, e_b, v_b
            O=B

        self.delay = len(regLayers.keys())

        
        

        if self.delay > 0:
            ready = Signal()
            m.d.comb += self.input_stream.ready.eq(ready)

            ready = [ready]
            for j, l in enumerate(regLayers.keys()):
                aE, aV, bE, bV = regLayers[l]
                wA = [len(e) for e in aE]
                wB = [len(e) for e in bE]
                #print("reg", l, wA)
                assert wA == wB, f"Thses should match. {i} {l} {wA} {wB}"

                newReady = []
                l_ready = []
                readyHere = Signal()
                for i in range(len(aV)):
                    m.submodules[f"reg{l}_{i}"] = reg = StreamReg(T=BasicStreamInterface, payload_width=wA[i], valid_width=1, optimized_valid_in=False, optimized_valid_out=False, use_double_buffering=(j % self.db_stride) == self.db_stride//2, max_width=128)
                    m.d.comb += [
                        reg.si.payload.eq(aE[i]),
                        reg.si.valid.eq(aV[i] & readyHere),
                        bE[i].eq(reg.so.payload),
                        bV[i].eq(reg.so.valid)
                    ]
                    l_ready.append(reg.si.ready)
                    newReady.append(reg.so.ready)
                m.d.comb += readyHere.eq(Cat(*l_ready).all())
                m.d.comb += [r.eq(readyHere) for r in ready]
                ready = newReady
            m.d.comb += [r.eq(self.output_stream.ready) for r in ready]
        else:
            m.d.comb += self.input_stream.ready.eq(self.output_stream.ready)
        
        m.d.comb += sum([[self.output_stream.valid[i].eq(v), self.output_stream.payload[i].eq(e)] for i, (v, e) in enumerate(O)], [])

        print(self.delay)

        return m


class SortingNet_merge_modular(Elaboratable):
    def __init__(self, comp:Callable[[Value, Value], Value], payload_width : int = 8, N : int = 8, registerStride=2, db_stride=1, useOptimal=True, d=0, level=0, inserted_registers=0):
        self.payload_width = payload_width
        self.comp = comp
        self.N = N
        self.registerStride = registerStride # >= 0 for addition of registers
        self.db_stride = db_stride
        self.useOptimal = useOptimal
        self.d = d
        self.level = level
        self.inserted_registers = inserted_registers

        self.input_stream = ArrayStreamInterface(name=f"input_stream_m_{N}_{level}_{inserted_registers}", payload_width=self.payload_width, valid_width=self.N)
        self.output_stream = ArrayStreamInterface(name=f"output_stream_m_{N}_{level}_{inserted_registers}", payload_width=self.payload_width, valid_width=self.N)

        
    
    def ports(self, select=0):
        deRecord = lambda r: [r[f] for f in r.fields]
        if select==0:
            return deRecord(self.input_stream) + deRecord(self.output_stream)
        if select==1:
            return deRecord(self.input_stream)
        if select==2:
            return deRecord(self.output_stream)

    def elaborate(self, platform):
        try:
            return self._m
        except AttributeError:
            self.gen()
            return self._m

    def gen(self):
        self._m = self._gen()

    def _gen(self):

        m = Module()

        if m.setPureIdentifier(type(self), self.payload_width, self.comp, self.N, self.useOptimal, self.registerStride, self.db_stride, self.d, self.level, self.inserted_registers):
            inputs = {f"{'o'if signal.name=='ready' else 'i'}_{signal.name}":signal for signal in self.ports(1)}
            outputs = {f"{'i'if signal.name=='ready' else 'o'}_{signal.name}":signal for signal in self.ports(2)}

            dom = {}
            if self.N > 1:
                dom["i_clk"]=ClockSignal("sync")
                dom["i_rst"]=ResetSignal("sync")

            m.submodules += Instance("dummy", **dom, **inputs, **outputs)
            return m
        
        print("Elaborating ", self.__class__.__name__, self)

        swap_cnt = [0,0]

        def swap2(T0, T1, d):
            
            nonlocal swap_cnt
            nonlocal m

            T0v, T0p = T0
            T1v, T1p = T1

            payload0_i = Signal(len(T0p))
            valid0_i = Signal()
            payload1_i = Signal(len(T1p))
            valid1_i = Signal()

            m.d.comb += [
                valid0_i.eq(T0v),
                payload0_i.eq(T0p),
                valid1_i.eq(T1v),
                payload1_i.eq(T1p)
            ]

            payload0_o = Signal(len(T0p))
            valid0_o = Signal()
            payload1_o = Signal(len(T1p))
            valid1_o = Signal()

            sm = Module()
            m.submodules[f"swap_{['up','down'][d]}_{swap_cnt[d]}"] = sm
            swap_cnt[d] += 1
            if sm.setPureIdentifier(type(self), m._generated["p_signature"], len(T0p), d):
                sm.submodules += Instance("dummy",
                    i_payload0_i = payload0_i,
                    i_valid0_i = valid0_i,
                    i_payload1_i = payload1_i,
                    i_valid1_i = valid1_i,
                    o_payload0_o = payload0_o,
                    o_valid0_o = valid0_o,
                    o_payload1_o = payload1_o,
                    o_valid1_o = valid1_o
                )
                return ((valid0_o, payload0_o), (valid1_o, payload1_o))


            swap = Signal()

            sm.d.comb += swap.eq(((self.comp(payload0_i, payload1_i) == Const(d, 1)) & valid1_i & valid0_i) | ((valid1_i & ~valid0_i) if d else (valid0_i & ~valid1_i)))

            with sm.If(swap):
                sm.d.comb += [
                    valid0_o.eq(valid1_i),
                    payload0_o.eq(payload1_i),
                    valid1_o.eq(valid0_i),
                    payload1_o.eq(payload0_i)
                ]
            with sm.Else():
                sm.d.comb += [
                    valid0_o.eq(valid0_i),
                    payload0_o.eq(payload0_i),
                    valid1_o.eq(valid1_i),
                    payload1_o.eq(payload1_i)
                ]

            return ((valid0_o, payload0_o), (valid1_o, payload1_o))

        if self.N <= 1:
            print(self, self.output_stream, self.input_stream)
            m.d.comb += self.output_stream.stream_eq(self.input_stream)
            
        else:
            k = self.N // 2
            next_layer = ArrayStreamInterface(name=f"merge_layer{self.level}", payload_width=self.payload_width, valid_width=self.N)
            A = [(self.input_stream.valid[i], self.input_stream.payload[i]) for i in range(self.N)]
            B = [(next_layer.valid[i], next_layer.payload[i]) for i in range(self.N)]
            m.d.comb += self.input_stream.ready.eq(next_layer.ready)
            for i in range(0, k):
                s0, s1 = swap2(A[i], A[i+k], self.d)
                m.d.comb += [
                    B[i][0].eq(s0[0]),
                    B[i][1].eq(s0[1]),
                    B[i+k][0].eq(s1[0]),
                    B[i+k][1].eq(s1[1])
                ]
            self.level += 1

            if self.registerStride > 0 and (self.level%self.registerStride) == (self.registerStride-1):
                m.submodules[f"reg{self.inserted_registers}"] = reg = StreamReg(ArrayStreamInterface, self.payload_width, self.N, use_double_buffering=(self.inserted_registers%self.db_stride) == (self.db_stride-1))
                self.inserted_registers += 1
                m.d.comb += reg.si.stream_eq(next_layer)
                intermerge_layer = reg.so
            else:
                intermerge_layer = next_layer

            if self.N > 2:            
                m.submodules.left_merge = left_merge = SortingNet_merge_modular(comp=self.comp, payload_width=self.payload_width, N=k,
                                               registerStride=self.registerStride, db_stride=self.db_stride,
                                               useOptimal=self.useOptimal, d=self.d, level=self.level, inserted_registers=self.inserted_registers)
                m.submodules.right_merge = right_merge = SortingNet_merge_modular(comp=self.comp, payload_width=self.payload_width, N=self.N-k,
                                                registerStride=self.registerStride, db_stride=self.db_stride,
                                                useOptimal=self.useOptimal, d=self.d, level=self.level, inserted_registers=self.inserted_registers)

                oready = Signal()
                m.d.comb += oready.eq(self.output_stream.ready)

                m.d.comb += [
                    intermerge_layer.ready.eq(left_merge.input_stream.ready & right_merge.input_stream.ready),
                    left_merge.output_stream.ready.eq(oready),
                    right_merge.output_stream.ready.eq(oready)
                ]
                for i in range(k):
                    m.d.comb += [
                        left_merge.input_stream.valid[i].eq(intermerge_layer.valid[i]),
                        left_merge.input_stream.payload[i].eq(intermerge_layer.payload[i]),
                        self.output_stream.valid[i].eq(left_merge.output_stream.valid[i]),
                        self.output_stream.payload[i].eq(left_merge.output_stream.payload[i])
                    ]
                for i, j in enumerate(range(k, self.N)):
                    m.d.comb += [
                        right_merge.input_stream.valid[i].eq(intermerge_layer.valid[j]),
                        right_merge.input_stream.payload[i].eq(intermerge_layer.payload[j]),
                        self.output_stream.valid[j].eq(right_merge.output_stream.valid[i]),
                        self.output_stream.payload[j].eq(right_merge.output_stream.payload[i])
                    ]

                left_merge.gen()
                right_merge.gen()

                self.level = max(left_merge.level, right_merge.level)
                self.inserted_registers = max(left_merge.inserted_registers, right_merge.inserted_registers)
            else:
                m.d.comb += self.output_stream.stream_eq(intermerge_layer)

        return m

class SortingNet_modular(Elaboratable):
    def __init__(self, comp:Callable[[Value, Value], Value], payload_width : int = 8, N : int = 8, registerStride=2, db_stride=1, useOptimal=True, d=0, level=0, inserted_registers=0):
        self.payload_width = payload_width
        self.comp = comp
        self.N = N
        self.registerStride = registerStride # >= 0 for addition of registers
        self.db_stride = db_stride
        self.useOptimal = useOptimal
        self.d = d
        self.level = level
        self.inserted_registers = inserted_registers

        self.input_stream = ArrayStreamInterface(name=f"input_stream_s_{N}_{level}_{inserted_registers}", payload_width=self.payload_width, valid_width=self.N)
        self.output_stream = ArrayStreamInterface(name=f"output_stream_s_{N}_{level}_{inserted_registers}", payload_width=self.payload_width, valid_width=self.N)
    
    def ports(self, select=0):
        deRecord = lambda r: [r[f] for f in r.fields]
        if select==0:
            return deRecord(self.input_stream) + deRecord(self.output_stream)
        if select==1:
            return deRecord(self.input_stream)
        if select==2:
            return deRecord(self.output_stream)

    def elaborate(self, platform):
        try:
            return self._m
        except AttributeError:
            self.gen()
            return self._m

    def gen(self):
        self._m = self._gen()
    
    def _gen(self):

        m = Module()

        if m.setPureIdentifier(type(self), self.payload_width, self.comp, self.N, self.useOptimal, self.registerStride, self.db_stride, self.d, self.level, self.inserted_registers):
            inputs = {f"{'o' if signal.name=='ready' else 'i'}_{signal.name}":signal for signal in self.ports(1)}
            outputs = {f"{'i' if signal.name=='ready' else 'o'}_{signal.name}":signal for signal in self.ports(2)}
            
            dom = {}
            if self.N > 1:
                dom["i_clk"]=ClockSignal("sync")
                dom["i_rst"]=ResetSignal("sync")

            m.submodules += Instance("dummy", **dom, **inputs, **outputs)
            return m
        
        print("Elaborating ", self.__class__.__name__, self)

        swap_cnt = [0,0]

        def swap2(T0, T1, d):
            
            nonlocal swap_cnt
            nonlocal m

            T0v, T0p = T0
            T1v, T1p = T1

            payload0_i = Signal(len(T0p))
            valid0_i = Signal()
            payload1_i = Signal(len(T1p))
            valid1_i = Signal()

            m.d.comb += [
                valid0_i.eq(T0v),
                payload0_i.eq(T0p),
                valid1_i.eq(T1v),
                payload1_i.eq(T1p)
            ]

            payload0_o = Signal(len(T0p))
            valid0_o = Signal()
            payload1_o = Signal(len(T1p))
            valid1_o = Signal()

            sm = Module()
            m.submodules[f"swap_{['up','down'][d]}_{swap_cnt[d]}"] = sm
            swap_cnt[d] += 1
            if sm.setPureIdentifier(type(self), m._generated["p_signature"], len(T0p), d):
                sm.submodules += Instance("dummy",
                    i_payload0_i = payload0_i,
                    i_valid0_i = valid0_i,
                    i_payload1_i = payload1_i,
                    i_valid1_i = valid1_i,
                    o_payload0_o = payload0_o,
                    o_valid0_o = valid0_o,
                    o_payload1_o = payload1_o,
                    o_valid1_o = valid1_o
                )
                return ((valid0_o, payload0_o), (valid1_o, payload1_o))


            swap = Signal()

            sm.d.comb += swap.eq(((self.comp(payload0_i, payload1_i) == Const(d, 1)) & valid1_i & valid0_i) | ((valid1_i & ~valid0_i) if d else (valid0_i & ~valid1_i)))

            with sm.If(swap):
                sm.d.comb += [
                    valid0_o.eq(valid1_i),
                    payload0_o.eq(payload1_i),
                    valid1_o.eq(valid0_i),
                    payload1_o.eq(payload0_i)
                ]
            with sm.Else():
                sm.d.comb += [
                    valid0_o.eq(valid0_i),
                    payload0_o.eq(payload0_i),
                    valid1_o.eq(valid1_i),
                    payload1_o.eq(payload1_i)
                ]

            return ((valid0_o, payload0_o), (valid1_o, payload1_o))
        

        if self.N <= 1:
            m.d.comb += self.output_stream.stream_eq(self.input_stream)
        elif self.useOptimal and (self.N in perfectSortings.keys()):
            sorter = perfectSortings[self.N]
            last_layer = self.input_stream
            for layer in sorter:
                next_layer = ArrayStreamInterface(name=f"sorting_layer{self.level}", payload_width=self.payload_width, valid_width=self.N)
                used_indexes = []
                A = [(last_layer.valid[i], last_layer.payload[i]) for i in range(self.N)]
                for swap in layer:
                    i0, i1 = swap
                    used_indexes += [i0, i1]
                    s0, s1 = swap2(A[i0], A[i1], self.d)
                    m.d.comb += [
                        next_layer.valid[i0].eq(s0[0]),
                        next_layer.payload[i0].eq(s0[1]),
                        next_layer.valid[i1].eq(s1[0]),
                        next_layer.payload[i1].eq(s1[1])
                    ]
                for i in range(self.N):
                    if i not in used_indexes:
                        m.d.comb += [
                            next_layer.valid[i].eq(A[i][0]),
                            next_layer.payload[i].eq(A[i][1])
                        ]
                m.d.comb += last_layer.ready.eq(next_layer.ready)
                self.level += 1
                if self.registerStride > 0 and (self.level%self.registerStride) == (self.registerStride-1):
                    m.submodules[f"reg{self.inserted_registers}"] = reg = StreamReg(ArrayStreamInterface, self.payload_width, self.N, use_double_buffering=(self.inserted_registers%self.db_stride) == (self.db_stride-1))
                    self.inserted_registers += 1
                    m.d.comb += reg.si.stream_eq(next_layer)
                    last_layer = reg.so
                else:
                    last_layer = next_layer
            m.d.comb += self.output_stream.stream_eq(last_layer)
        else:

            k = self.N//2
            left_sort = SortingNet_modular(comp=self.comp, payload_width=self.payload_width, N=k,
                                           registerStride=self.registerStride, db_stride=self.db_stride,
                                           useOptimal=self.useOptimal, d=1, level=self.level, inserted_registers=self.inserted_registers)
            right_sort = SortingNet_modular(comp=self.comp, payload_width=self.payload_width, N=self.N-k,
                                            registerStride=self.registerStride, db_stride=self.db_stride,
                                            useOptimal=self.useOptimal, d=0, level=self.level, inserted_registers=self.inserted_registers)
            m.submodules.left_sort = left_sort
            m.submodules.right_sort = right_sort
            toMerge = ArrayStreamInterface(payload_width=self.payload_width, valid_width=self.N)
            m.d.comb += [
                self.input_stream.ready.eq(left_sort.input_stream.ready & right_sort.input_stream.ready),
                left_sort.output_stream.ready.eq(toMerge.ready),
                right_sort.output_stream.ready.eq(toMerge.ready)
            ]
            for i in range(k):
                m.d.comb += [
                    left_sort.input_stream.valid[i].eq(self.input_stream.valid[i]),
                    left_sort.input_stream.payload[i].eq(self.input_stream.payload[i]),
                    toMerge.valid[i].eq(left_sort.output_stream.valid[i]),
                    toMerge.payload[i].eq(left_sort.output_stream.payload[i])
                ]
            for i, j in enumerate(range(k, self.N)):
                m.d.comb += [
                    right_sort.input_stream.valid[i].eq(self.input_stream.valid[j]),
                    right_sort.input_stream.payload[i].eq(self.input_stream.payload[j]),
                    toMerge.valid[j].eq(right_sort.output_stream.valid[i]),
                    toMerge.payload[j].eq(right_sort.output_stream.payload[i])
                ]
            left_sort.gen()
            right_sort.gen()
            merge = SortingNet_merge_modular(comp=self.comp, payload_width=self.payload_width, N=self.N,
                                                                  registerStride=self.registerStride, db_stride=self.db_stride,
                                                                  useOptimal=self.useOptimal, d=self.d, level=max(left_sort.level, right_sort.level),
                                                                  inserted_registers=max(left_sort.inserted_registers, right_sort.inserted_registers))
            m.submodules.merge = merge
            m.d.comb += [
                self.output_stream.stream_eq(merge.output_stream),
                merge.input_stream.stream_eq(toMerge)
            ]
            #print(k, self.N, merge.output_stream)
            merge.gen()
            self.level = merge.level
            self.inserted_registers = merge.inserted_registers
        return m

    
        



def dummyMerge(m, An, Bn, A, B, nA, nAv):

    mod = Module()
    mod.setPureIdentifier(dummyMerge, len(A))


    l = StructLayout({"key":6, "data":len(A)-6})
    nA_i = Signal(l)
    nB_i = Const(0, len(nA_i.as_value()))
    iA = Signal(l)
    iB = Signal(l)
    v_i = Signal()

    mod.d.comb += [
        nA_i.key.eq(iA.key),
        nA_i.data.eq(iA.data + iB.data),
        v_i.eq(Const(0,1))
    ]

    m.submodules += mod
    m.d.comb += [
        iA.eq(A),
        iB.eq(B),
        nA.eq(nA_i),
        nAv.eq(1)
    ]





class MergeNet(Elaboratable):

    def __init__(self, comp:Callable[[Value, Value], Value], eq:Callable[[Value, Value], Value], element_width : int = 8, base_width : int = 16, N : int = 8, registerStride=2, endOnReg=True, useOptimal=True, mergeFunc : Callable[[Module, int, int, Value, Value, Value, Value, Value],None] = dummyMerge):
        self.element_width = element_width
        self.base_width = base_width
        self.comp = comp
        self.eq = eq
        self.mergeFunc = mergeFunc
        self.N = N
        self.registerStride = registerStride # >= 0 for addition of registers
        self.delay = 0 #Will be updated with the number of register levels added
        self.endOnReg = endOnReg
        self.useOptimal = useOptimal

        self.input_stream = ArrayStreamInterface(payload_width=self.base_width + self.element_width, valid_width=self.N)
        self.output_stream = ArrayStreamInterface(payload_width=self.base_width + self.N * self.element_width, valid_width=self.N)
    
    def ports(self, select=0):
        deRecord = lambda r: [r[f] for f in r.fields]
        if select==0:
            return deRecord(self.input_stream) + deRecord(self.output_stream)
        if select==1:
            return deRecord(self.input_stream)
        if select==2:
            return deRecord(self.output_stream)

    def elaborate(self, platform):

        m = Module()

        if m.setPureIdentifier(type(self), self.base_width, self.element_width, self.comp, self.eq, self.mergeFunc, self.N, self.useOptimal, self.registerStride, self.endOnReg):
            inputs = {f"i_{signal.name}":signal for signal in self.ports(1)}
            outputs = {f"o_{signal.name}":signal for signal in self.ports(2)}
            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"), **inputs, **outputs)
            return m
        
        print("Elaborating ", self.__class__.__name__, self)

        regLayers = OrderedDict()

        def swap2(T0, T1, d):
            T0v, T0p, T0n = T0
            T1v, T1p, T1n = T1


            n = min(T0n + T1n, self.N)
            swap = Signal()
            e = Signal()
            nV0 = Record([("valid", 1), ("payload", unsigned(self.base_width + n * self.element_width))])
            nVk = Record([("valid", 1), ("payload", unsigned(self.base_width + n * self.element_width))])
                    
            m0 = Signal(self.base_width + n * self.element_width)
            m0v = Signal()

            self.mergeFunc(m, T0n, T1n, T0p, T1p, m0, m0v)
            m.d.comb += [
                e.eq(self.eq(T0p[:self.base_width], T1p[:self.base_width]) & T1v & T0v),
                nV0.valid.eq(Mux(e, m0v, T0v)),
                nVk.valid.eq(Mux(e, 0, T1v)),
                nV0.payload.eq(Mux(e, m0, T0p)),
                nVk.payload.eq(T1p)
            ]

            if d:
                m.d.comb += swap.eq((self.comp(T0p[:self.base_width], T1p[:self.base_width]) & T1v & T0v) | (nV0.valid & ~nVk.valid))
            else:
                m.d.comb += swap.eq((self.comp(T1p[:self.base_width], T0p[:self.base_width]) & T1v & T0v) | (nVk.valid & ~nV0.valid))

            ret = ((Signal(), Signal(self.base_width + n * self.element_width), n), (Signal(), Signal(self.base_width + n * self.element_width), n))
            with m.If(swap):
                m.d.comb += [
                    ret[0][0].eq(nVk.valid),
                    ret[0][1].eq(nVk.payload),
                    ret[1][0].eq(nV0.valid),
                    ret[1][1].eq(nV0.payload)
                ]
            with m.Else():
                m.d.comb += [
                    ret[1][0].eq(nVk.valid),
                    ret[1][1].eq(nVk.payload),
                    ret[0][0].eq(nV0.valid),
                    ret[0][1].eq(nV0.payload)
                ]
            return ret
        
        def bSort(A, d, level=0):
            cnt = len(A)
            if cnt <= 1:
                return A, level
            elif self.useOptimal and (cnt in perfectSortings.keys()):
                sorter = perfectSortings[cnt]
                for layer in sorter:
                    for swap in layer:
                        i0, i1 = swap
                        A[i0], A[i1] = swap2(A[i0], A[i1], d)
                    level += 1
                    if self.registerStride > 0 and (level%self.registerStride) == (self.registerStride-1):
                        B = [(Signal(), Signal(len(A[i][1])), A[i][2]) for i in range(cnt)]

                        s = regLayers.get(level,None)
                        v_b, e_b, n_b = zip(*B)
                        v_a, e_a, n_a = zip(*A)

                        if s == None:
                            regLayers[level] = e_a, v_a, e_b, v_b
                        else:
                            aE, aV, bE, bV = s
                            regLayers[level] = aE+e_a, aV+v_a, bE+e_b, bV+v_b

                        A = B
                
                return A, level
            else:
                k = cnt//2
                L, lev_l = bSort(A[:k], 1, level=level)
                R, lev_r = bSort(A[k:], 0, level=level)
                return bMerge(L+R, d, level=max(lev_l, lev_r))
            

    
        def bMerge(A, d, level=0):
            cnt = len(A)
            if cnt > 1:
                k = cnt//2
                B = [(Signal(), Signal(len(A[i][1])), A[i][2]) for i in range(cnt)]

                for i in range(0, k):
                    B[i], B[i+k] = swap2(A[i], A[i+k], d)
                level += 1

                if self.registerStride > 0 and (level%self.registerStride) == (self.registerStride-1):
                    C = [(Signal(), Signal(len(B[i][1])), B[i][2]) for i in range(cnt)]
                    s = regLayers.get(level,None)
                    v_b, e_b, n_b = zip(*C)
                    v_a, e_a, n_a = zip(*B)

                    if s == None:
                        regLayers[level] = e_a, v_a, e_b, v_b
                    else:
                        aE, aV, bE, bV = s
                        regLayers[level] = aE+e_a, aV+v_a, bE+e_b, bV+v_b
                    B = C
                
                L, lev_l = bMerge(B[:k], d, level=level)
                R, lev_r = bMerge(B[k:], d, level=level)


                return L+R, max(lev_l, lev_r)
            return A, level

        O, l = bSort([(self.input_stream.valid[i] & self.input_stream.ready, self.input_stream.payload[i], 1) for i in range(len(self.input_stream.valid))], 1)

        if self.endOnReg and (l not in regLayers):
            B = [(Signal(), Signal(len(O[i][1])), O[i][2]) for i in range(len(O))]
            v_b, e_b, n_b = zip(*B)
            v_a, e_a, n_a = zip(*O)
            regLayers[l] = e_a, v_a, e_b, v_b
            O=B

        self.delay = len(regLayers.keys())

        
        

        if self.delay > 0:
            ready = Signal()
            m.d.comb += self.input_stream.ready.eq(ready)

            ready = [ready]
            for i, l in enumerate(regLayers.keys()):
                aE, aV, bE, bV = regLayers[l]
                wA = [len(e) for e in aE]
                wB = [len(e) for e in bE]
                assert wA == wB, f"Thses should match. {i} {l} {wA} {wB}"

                newReady = []
                l_ready = []
                readyHere = Signal()
                for i in range(len(aV)):
                    m.submodules[f"reg{l}_{i}"] = reg = StreamReg(T=BasicStreamInterface, payload_width=wA[i], valid_width=1, optimized_valid_in=False, optimized_valid_out=False, use_double_buffering=True, max_width=128)
                    m.d.comb += [
                        reg.si.payload.eq(aE[i]),
                        reg.si.valid.eq(aV[i] & readyHere),
                        bE[i].eq(reg.so.payload),
                        bV[i].eq(reg.so.valid)
                    ]
                    l_ready.append(reg.si.ready)
                    newReady.append(reg.so.ready)
                m.d.comb += readyHere.eq(Cat(*l_ready).all())
                m.d.comb += [r.eq(readyHere) for r in ready]
                ready = newReady
            m.d.comb += [r.eq(self.output_stream.ready) for r in ready]
        else:
            m.d.comb += self.input_stream.ready.eq(self.output_stream.ready)
        
        m.d.comb += sum([[self.output_stream.valid[i].eq(v), self.output_stream.payload[i].eq(e)] for i, (v, e, n) in enumerate(O)], [])

        return m
    



class SortingNetFormalTest(FHDLTestCase):
    def test_formal(self):
        self.assertFormal(SortingNet(element_width=4, comp_slice=slice(None,3), N=4, dir=0), mode="prove", depth=25)





class CombinedTest(FHDLTestCase):
    def test_basic(self):
        m = Module()

        m.submodules.s_dut = s_net = SortingNet(element_width=12, N=8)

        m.submodules.m_dut = merger = MergeNet(element_width=12, N=8)

        keyI = [Signal(4, name=f"ki{i}") for i in range(8)]
        keyO = [Signal(4, name=f"ko{i}") for i in range(8)]

        dataI = [Signal(8, name=f"di{i}") for i in range(8)]
        dataO = [Signal(8, name=f"do{i}") for i in range(8)]

        for i in range(8):
            m.d.comb += [
                merger.i_arr[i].data[:4].eq(keyI[i]),
                merger.i_arr[i].data[4:].eq(dataI[i]),
                s_net.i_arr[i].data.eq(merger.o_arr[i].data),
                s_net.i_arr[i].valid.eq(merger.o_arr[i].valid),
                keyO[i].eq(s_net.o_arr[i].data[:4]),
                dataO[i].eq(s_net.o_arr[i].data[4:])
            ]
        
        sim = Simulator(m)

        def stimuli():
            for r in [merger.i_arr[i].valid.eq(1) for i in range(8)]:
                yield r
            for r in [dataI[i].eq(1) for i in range(8)]:
                yield r
            
            yield keyI[0].eq(2)
            yield keyI[1].eq(2)
            yield keyI[2].eq(5)
            yield keyI[3].eq(6)
            yield keyI[4].eq(1)
            yield keyI[5].eq(9)
            yield keyI[6].eq(5)
            yield keyI[7].eq(2)
            yield Delay(1e-6)
        
        sim.add_process(stimuli)
        with sim.write_vcd("merge.vcd", "merge.gtkw", traces=[merger.i_arr[i].valid for i in range(8)]+[s_net.o_arr[i].valid for i in range(8)]+dataI+keyI+dataO+keyO):
            sim.run()



def omegaNet(inputs, outputs):
    assert inputs >= outputs

    p2 = (1 << cl2(inputs)) == inputs 

    steps = cl2(inputs)

    indirection = [0]*inputs
    for i, j in enumerate(sum((list(z) for z in zip(range(0,inputs//2), range(inputs//2,inputs))), [])):
        indirection[j] = i

    def addr(a):
        #Rotate addr bits 1 step left
        if p2:
            assert indirection[a] == ((a & ((1<<(steps-1))-1))<<1) | ((a & (1 << (steps-1))) != 0)
        
        return indirection[a]


    mask = ((1<<steps)-1) & ~1
    layers = []
    for _ in range(steps):
        layer = []
        for i in range(inputs//2):
            a = (addr(i*2) & mask) >> 1
            b = (addr(i*2 + 1) & mask) >> 1
            layer.append([0, a, b])
        layers.append(layer)
    layers.append([[0, i, i] for i in range(inputs//2)])
    
    use = 2#1 if outputs_l2 < inputs_l2 else 2
    offset = (inputs//2 - outputs//use) // 2 #0
    shift = 1#(inputs_l2 - outputs_l2)
    for i in range(0, shift*outputs//use, shift):
        layers[steps][i+offset][0] = use
    
    for s in reversed(range(steps)):
        for i in range(len(layers[s])):
            layers[s][i][0] = (layers[s+1][layers[s][i][1]][0] != 0) + (layers[s+1][layers[s][i][2]][0] != 0)
    
    return layers


class DistributionNet(Elaboratable):
    def __init__(self, nrOfInputs=8, nrOfOutputs=8, T=BasicStreamInterface, payload_width=32, valid_width=1, max_width=256, optimized_valid_in=False, optimized_valid_out=False, extra_fields=[]):
        self.regSettings = {"T":T, "payload_width":payload_width, "valid_width":valid_width , "max_width":max_width, "optimized_valid_in":optimized_valid_in, "optimized_valid_out":optimized_valid_out, "extra_fields":extra_fields}
        self.nrOfInputs = nrOfInputs
        self.nrOfOutputs = nrOfOutputs

        self.inputs = [T(name=f"input{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if optimized_valid_in else [])+extra_fields ) for i in range(self.nrOfInputs)]
        self.outputs = [T(name=f"output{i}", payload_width=payload_width, valid_width=valid_width, extra_fields=([('o_valid', 1)] if optimized_valid_out else [])+extra_fields ) for i in range(self.nrOfOutputs)]
    
    def elaborate(self, platform):
        m = Module()

        settings=tuple(tuple(s) if isinstance(s, list) else s for s in self.regSettings.values())
        if m.setPureIdentifier(type(self), self.nrOfInputs, self.nrOfOutputs, settings):
            ports = {}
            for i, S in enumerate(self.inputs):
                for f in S.fields:
                    d = "o" if f == "ready" else "i"
                    ports[f"{d}_input{i}_{f}"] = S[f]
            for i, S in enumerate(self.outputs):
                for f in S.fields:
                    d = "i" if f == "ready" else "o"
                    ports[f"{d}_output{i}_{f}"] = S[f]

            m.submodules += Instance("dummy", i_clk=ClockSignal("sync"), i_rst=ResetSignal("sync"), **ports)
            return m
        
        layers = omegaNet(self.nrOfInputs, self.nrOfOutputs)

        active_layer = [(self.inputs[2*i], self.inputs[2*i+1]) for i in range(self.nrOfInputs//2)]
        for i in range(len(layers)-1):
            new_layer = []
            routers = []
            for j in range(len(layers[i+1])):
                if layers[i+1][j][0] == 1:
                    m.submodules[f"join_router{i}_{j}"] = router = StreamJoin(**self.regSettings)
                    routers.append(router)
                    new_layer.append((router.so,))
                elif layers[i+1][j][0] == 2:
                    m.submodules[f"distribute_router{i}_{j}"] = router = StreamDistribute_2to2(**self.regSettings)
                    routers.append(router)
                    new_layer.append(tuple(router.so))
                else:
                    new_layer.append(None)
                    routers.append(None)
            
            for j in range(len(layers[i])):
                if layers[i][j][0] == 1:
                    if layers[i+1][layers[i][j][1]][0] != 0:
                        m.d.comb += routers[layers[i][j][1]].si[2*j >= self.nrOfInputs//2].stream_eq(active_layer[j][0])
                    else:
                        m.d.comb += routers[layers[i][j][2]].si[2*j+1 >= self.nrOfInputs//2].stream_eq(active_layer[j][0])
                elif layers[i][j][0] == 2:
                    m.d.comb += [routers[layers[i][j][1]].si[2*j >= self.nrOfInputs//2].stream_eq(active_layer[j][0]),
                                 routers[layers[i][j][2]].si[2*j+1 >= self.nrOfInputs//2].stream_eq(active_layer[j][1])]
            active_layer = new_layer
        
        j = 0
        for r in active_layer:
            if r:
                assert j < self.nrOfOutputs
                for p in r:
                    m.d.comb += self.outputs[j].stream_eq(p)
                    j += 1
        assert j == self.nrOfOutputs, str(j)

        return m