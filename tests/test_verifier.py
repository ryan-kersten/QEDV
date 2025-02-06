import itertools
import unittest
from errno import errorcode

import numpy as np

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
        self.assertTrue(Verifier.stabalizerCheck(code, QuantumError({1,0}))[0])

    def testbruteForceTest(self):
        def generate_matrices(distance=3):
            for matrix in itertools.product([0, 1], repeat=distance ** 2):
                yield np.array(matrix).reshape(distance, distance)

        for distance in range(3,5):
            for possibility in generate_matrices(distance):
                code = SurfaceCode(distance)
                flattened = list(itertools.chain(*possibility))
                python_int_list = [int(x) for x in flattened]
                result_set = {index for index, value in enumerate(python_int_list) if value == 1}
                error = QuantumError(result_set)
                brute = Verifier._BruteForcestabilizerCheck(code, error)
                reduction =  Verifier.stabalizerCheck(code, error)[0]
                self.assertTrue(brute is reduction)

