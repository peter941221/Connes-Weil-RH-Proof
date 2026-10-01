"""2338: rigorous solve and matrix-norm negative controls."""
import unittest

from flint import acb_mat, arb, ctx

from routea_exact_interpolation_repair_2338 import get_matrix_infinity_bound


class ExactRepairTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 320

    def test_known_exact_solution_is_enclosed(self):
        matrix = acb_mat([[2, 1], [1, 3]])
        solution = matrix.solve(acb_mat([[1], [2]]), algorithm="precond")
        self.assertTrue(solution[0, 0].real.contains(arb("1/5")))
        self.assertTrue(solution[1, 0].real.contains(arb("3/5")))

    def test_singular_matrix_is_rejected(self):
        with self.assertRaises(ZeroDivisionError):
            acb_mat([[1, 1], [2, 2]]).solve(acb_mat([[1], [2]]), algorithm="precond")

    def test_complex_matrix_norm_uses_full_modulus(self):
        matrix = acb_mat([[3 + 4j, 1], [0, -2]])
        bound = get_matrix_infinity_bound(matrix)
        self.assertTrue(bound >= 6)
        self.assertTrue(bound < arb("601/100"))

    def test_matrix_norm_uses_upper_endpoint_of_error_ball(self):
        matrix = acb_mat([[arb(1, "1/10")]])
        bound = get_matrix_infinity_bound(matrix)
        self.assertTrue(bound >= arb("11/10"))
        self.assertTrue(bound.is_exact())

    def test_neumann_identity_control_has_zero_defect(self):
        matrix = acb_mat([[2, 0], [0, 4]])
        approximate_inverse = matrix.inv().mid()
        identity = acb_mat([[1, 0], [0, 1]])
        self.assertTrue(get_matrix_infinity_bound(identity - approximate_inverse * matrix).is_zero())

    def test_wrong_inverse_does_not_pass_neumann_gate(self):
        matrix = acb_mat([[2, 0], [0, 4]])
        wrong_inverse = acb_mat([[1, 0], [0, 1]])
        identity = acb_mat([[1, 0], [0, 1]])
        bound = get_matrix_infinity_bound(identity - wrong_inverse * matrix)
        self.assertFalse(bound < arb("1/2"))


if __name__ == "__main__":
    unittest.main()
