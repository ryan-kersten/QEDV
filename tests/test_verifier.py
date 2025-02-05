import unittest
from errno import errorcode

from QEDV_lib import Stabilizer, ErrorCode, QuantumError
from QEDV_lib.error_codes import SurfaceCode
from QEDV_lib.verifier import Verifier


class testStabalizer(unittest.TestCase):
    def setUp(self):
        ...
    def testParityCheck(self):
        error = QuantumError({1})
        code = SurfaceCode(3)
        stabalizers = code.getStabilizers()
        stabalizer = next((s for s in stabalizers if s.getQubits() == {0,1}), None)
        stabalizer.setParity(1)
        self.assertFalse(Verifier.parityChecker(stabalizers, error))

        error.qubits = {1,2}
        self.assertTrue(Verifier.parityChecker(stabalizers, error))

        error.qubits = {0, 2}
        self.assertFalse(Verifier.parityChecker(stabalizers, error))

        error.qubits = {1,2,3,4,5,6,7,8}
        self.assertTrue(Verifier.parityChecker(stabalizers, error))
    def testStabalizerSet(self):
        code = SurfaceCode(3)
        self.assertFalse(Verifier.stabalizerCheck(code, QuantumError({1}))[0])
        self.assertTrue(Verifier.stabalizerCheck(code, QuantumError({1,2}))[0])