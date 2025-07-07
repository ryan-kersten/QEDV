import random

import qldpc.codes
import stim

from QEDV_lib import ErrorCode, QuantumError

from qldpc.codes.quantum import *

class SurfaceCode(ErrorCode):
    def __init__(self, distance):
        self.qubits = distance**2
        surCode = qldpc.codes.SurfaceCode(distance)
        self.checkMatrix = qldpc.codes.SurfaceCode(distance).matrix
        self.x_stab = ErrorCode.checkToStab(surCode.code_x.matrix)
        self.z_stab = ErrorCode.checkToStab(surCode.code_z.matrix)
