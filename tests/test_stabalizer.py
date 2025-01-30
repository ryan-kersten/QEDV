import unittest
from QEDV_lib.error_codes import SurfaceCode


class testStabalizer(unittest.TestCase):
    def setUp(self):
        ...
    def test1(self):
        code = SurfaceCode(3)
        correct = {{0, 1}, {1, 2, 4, 5}, {3, 4, 6, 7}, {7, 8}}
