import unittest

from QEDV_lib.error_codes import SurfaceCode


class testStabalizer(unittest.TestCase):
    def setUp(self):
        ...
    def testSurfaceCode(self):
        code3 = SurfaceCode(3)
        print(code3.x_stab)
        # self.assertEqual(code3.x_stab, [{}])
        correctz = [{0,1},{3,4,6,7},{1,2,4,5},{7,8}]


    def testSurfaceCode2(self):
        code5Input = [{0, 1}, {2, 3}, {1, 2, 6, 7}, {3, 4, 8, 9}, {5, 6, 10, 11}, {7, 8, 12, 13}, {11, 12, 16, 17},
                 {13, 14, 18, 19}, {15, 16, 20, 21}, {17, 18, 22, 23}, {21, 22}, {23, 24}]
        code5 = {Stabilizer(qubits) for qubits in code5Input}
        self.assertEqual(SurfaceCode(5).stabilizers, code5)



