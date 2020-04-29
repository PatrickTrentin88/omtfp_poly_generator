"""An OMT Problem Generator"""

#!/bin/env python3

import random
from environment import Environment

class Poly:
    """An OMT Problem Generator"""

    RM = Environment.RoundingMode.RNE

    def __init__(self, ebits, sbits):
        """Initializes Poly with the required FP format"""
        self._env = Environment()
        self._fmt = (ebits, sbits)
        self._tb = ebits + sbits

    def problem(self, order_n):
        """Generates a Poly OMT problem of order `order_n'"""
        self._env.set_option("opt.verbose", "true")
        x_var = self.get_x()
        a_vector = self.__get_vector_random_costants(order_n)
        fx_var = self.get_fx(x_var, a_vector, order_n)
        gx_var = self.get_gx(x_var, a_vector, order_n)
        goal = self.get_goal("eps", fx_var, gx_var)
        self._env.maximize(goal)
        self._env.check_sat()
        self._env.get_objectives()
        self._env.get_model()

    def get_x(self):
        """Declares a bounded 'x' variable"""
        self._env.comment("x definition")
        x_var = self._env.declare_fp_var("x", self._fmt)
        min_fp = self._env.define_fp_var("min_fp", self._fmt,
                                         self._env.make_min_fp(self._fmt))
        max_fp = self._env.define_fp_var("min_fp", self._fmt,
                                         self._env.make_max_fp(self._fmt))
        lb_cs = self._env.make_fp_leq(min_fp, x_var)
        ub_cs = self._env.make_fp_leq(x_var, max_fp)
        self._env.assert_formula(lb_cs)
        self._env.assert_formula(ub_cs)
        return x_var

    def get_goal(self, name, fx_var, gx_var):
        """Declares the objective function"""
        self._env.comment("goal definition")
        abs_fx = self._env.define_fp_var("abs_fx", self._fmt,
                                         self._env.make_fp_abs(fx_var))
        abs_gx = self._env.define_fp_var("abs_gx", self._fmt,
                                         self._env.make_fp_abs(gx_var))
        max_var = self._env.define_fp_var("max", self._fmt,
                                          self._env.make_fp_max(abs_fx, abs_gx))
        sub = self._env.define_fp_var("sub", self._fmt,
                                      self._env.make_fp_sub(Poly.RM, fx_var, gx_var))
        abs_sub = self._env.define_fp_var("abs_sub", self._fmt,
                                          self._env.make_fp_abs(sub))
        eps = self._env.declare_fp_var(name, self._fmt)
        eps_mul_max = self._env.define_fp_var("eps_mul_max", self._fmt,
                                              self._env.make_fp_mul(Poly.RM, eps,
                                                                    max_var))
        gt_cs = self._env.make_fp_gt(abs_sub, eps_mul_max)
        self._env.assert_formula(gt_cs)
        return eps

    def get_fx(self, x_var, a_vector, order_n):
        """Encodes f(x)"""
        self._env.comment("f(x) definition")
        x_vector = self.__get_vector_defs(x_var, order_n - 1)
        # a_n_MUL_x_n
        addends = [a_vector[0]]
        for a_const, x_el, i in zip(a_vector[1:], x_vector, range(1, len(x_vector)+1)):
            name = "fx_MUL_{0}".format(i)
            mul = self._env.make_fp_mul(Poly.RM, a_const, x_el)
            self._env.define_fp_var(name, self._fmt, mul)
            addends.append(name)
        # a_i_MUL_x_i + a_i+1_MUL_x_i+1
        cur_sum = addends[0]
        for i in range(1, len(addends)):
            name = "fx_SUM_{0}".format(i)
            expr = self._env.make_fp_add(Poly.RM, cur_sum, addends[i])
            cur_sum = self._env.define_fp_var(name, self._fmt, expr)
        # fx
        fx_var = self._env.define_fp_var("fx", self._fmt, cur_sum)
        return fx_var

    def get_gx(self, x_var, a_vector, order_n):
        """Encodes g(x)"""
        self._env.comment("g(x) definition")
        a_vector = a_vector[::-1]
        cur_sum = a_vector[0]
        for a_const, i in zip(a_vector[1:], reversed(range(order_n))):
            name_p = "gx_MUL_{0}".format(i)
            name_s = "gx_SUM_{0}".format(i)
            expr = self._env.make_fp_mul(Poly.RM, x_var, cur_sum)
            cur_prod = self._env.define_fp_var(name_p, self._fmt, expr)
            expr = self._env.make_fp_add(Poly.RM, a_const, cur_prod)
            cur_sum = self._env.define_fp_var(name_s, self._fmt, expr)
        # gx
        gx_var = self._env.define_fp_var("gx", self._fmt, cur_sum)
        return gx_var

    def __get_vector_defs(self, x_var, order_n):
        """Yields a vector of n elements of increasing powers of x"""
        ret = []
        if order_n > 0:
            ret.append(x_var)
            x_cur = x_var
            for i in range(2, order_n+1):
                name = "x_{0}".format(i)
                expr = self._env.make_fp_mul(Poly.RM, x_var, x_cur)
                x_cur = self._env.define_fp_var(name, self._fmt, expr)
                ret.append(x_cur)
        return ret

    def __get_vector_random_costants(self, order_n):
        """Yields a vector of n random constant FP values"""
        a_vector = [self.__gen_random_fp_constant() for i in range(order_n)]
        ret = []
        for i in range(0, order_n):
            name = "a_{0}".format(i)
            a_cur = self._env.define_fp_var(name, self._fmt, a_vector[i])
            ret.append(a_cur)
        return ret

    def __gen_random_fp_constant(self):
        """Yields a random FP value"""
        seq = "#b{0}".format(''.join(random.choice("01") for i in range(self._tb)))
        return self._env.make_bv_to_fp(seq, self._fmt)


def main():
    """A Test Function for class Polygen"""
    poly = Poly(5, 11)
    poly.problem(4)

if __name__ == '__main__':
    main()
