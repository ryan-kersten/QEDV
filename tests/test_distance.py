import unittest
import QEDV_lib.error_codes
import QEDV_lib.verifier
class Test_Distance(unittest.TestCase):

    def setUp(self):
        ...

    def test_basic(self):
        surface = QEDV_lib.error_codes.SurfaceCode(5)
        print("Testing surface code of legnth 3")
        print("X stabs are")
        print(surface.x_stab)
        print("Y stabs are")
        print(surface.z_stab)
        # val = QEDV_lib.verifier.minDistance(surface, 2)
        # self.assertTrue(val)
        rref = QEDV_lib.verifier.gottesmans(surface.checkMatrix)
        print(rref)
