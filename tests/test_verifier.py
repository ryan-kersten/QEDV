import unittest

from QEDV_lib import Stabilizer
from QEDV_lib.error_codes import SurfaceCode


class testStabalizer(unittest.TestCase):
    def setUp(self):
        ...
    def testSurfaceCode(self):
        code3 = SurfaceCode(3)
        code4 = SurfaceCode(4)
        correct = {Stabilizer({0, 1}), Stabilizer({1, 2, 4, 5}), Stabilizer({3, 4, 6, 7}), Stabilizer({7, 8})}
        self.assertEqual(code3.stabilizers, correct)
        self.assertNotEqual(code4.stabilizers, correct)
    def testSurfaceCode2(self):
        code5Input = [{0, 1}, {2, 3}, {1, 2, 6, 7}, {3, 4, 8, 9}, {5, 6, 10, 11}, {7, 8, 12, 13}, {11, 12, 16, 17},
                 {13, 14, 18, 19}, {15, 16, 20, 21}, {17, 18, 22, 23}, {21, 22}, {23, 24}]
        code5 = {Stabilizer(qubits) for qubits in code5Input}
        self.assertEqual(SurfaceCode(5).stabilizers, code5)



