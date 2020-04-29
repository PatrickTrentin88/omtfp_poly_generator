"""A dummy environment for encoding SMT-LIB problems"""

#!/bin/env python3

import enum
import re

class Environment: # pylint: disable=R0201,R0904
    """A dummy environment for encoding SMT-LIB problems"""

    ############################
    ############################
    ### COMMON FUNCTIONALITY ###
    ############################
    ############################

    def set_option(self, *args):
        """(set-option :config key=value)"""
        print("(set-option :config {0}={1})".format(*args))

    def push(self):
        """(push 1)"""
        print("(push)")

    def pop(self):
        """(pop 1)"""
        print("(push)")

    def assert_formula(self, *args):
        """(assert (and f1 ... fN))"""
        for arg in args:
            print("(assert {0})".format(arg))

    def minimize(self, *args):
        """(minimize term)"""
        print("(minimize {0})".format(*args))

    def maximize(self, *args):
        """(maximize term)"""
        print("(maximize {0})".format(*args))

    def check_sat(self):
        """(check-sat)"""
        print("(check-sat)")

    def get_objectives(self):
        """(get-objectives)"""
        print("(get-objectives)")

    def get_model(self):
        """(get-model)"""
        print("(get-model)")

    def get_model_value(self, *args):
        """(get-value (term1 ... termN))"""
        for arg in args:
            print("(get-value ({0}))".format(arg))

    def comment(self, *args):
        """; whatever"""
        for arg in args:
            print("; {0}".format(arg))

    ###########
    ###########
    ### EUF ###
    ###########
    ###########

    def make_equal(self, *args):
        """(= term1 term2)"""
        return "(= {0} {1})".format(*args)



    ######################
    ######################
    ### FLOATING POINT ###
    ######################
    ######################

    class RoundingMode(enum.Enum):
        """Floating Point Rounding Modes:
        RNE: roundNearestTiesToEven
        RNA: roundNearestTiesToAway
        RTP: roundTowardPositive
        RTN: roundTowardNegative
        RTZ: roundTowardZero"""
        RNE = 1     # roundNearestTiesToEven
        RNA = 2     # roundNearestTiesToAway
        RTP = 3     # roundTowardPositive
        RTN = 4     # roundTowardNegative
        RTZ = 5     # roundTowardZero

        def __str__(self):
            """String representation."""
            return self.name

    ###############
    # fp_fmt FORMAT #
    ###############

    def make_fp_fp_fmt(self, ebits, sbits):
        """(ebits, sbits)"""
        if ebits <= 1 or sbits <= 1:
            raise ValueError("ebits, sbits must be larger than 1.")
        return (ebits, sbits)

    def make_float16_fp_fmt(self):
        """; Float16 is a synonym for (_ FloatingPoint  5  11)"""
        return (5, 11)

    def make_float32_fp_fmt(self):
        """; Float32 is a synonym for (_ FloatingPoint  8  24)"""
        return (8, 24)

    def make_float64_fp_fmt(self):
        """; Float64 is a synonym for (_ FloatingPoint 11  53)"""
        return (11, 53)

    def make_float128_fp_fmt(self):
        """; Float128 is a synonym for (_ FloatingPoint 15 113)"""
        return (15, 113)


    ################
    # DECLARATIONS #
    ################

    def declare_fp_var(self, *args):
        """(declare-fun name () fp_fmt)"""
        print("(declare-fun {0} () (_ FloatingPoint {1} {2}))".format(args[0],
                                                                      args[1][0],
                                                                      args[1][1]))
        return args[0]


    def define_fp_var(self, *args):
        """(define-fun name () fp_fmt expr)"""
        print("(define-fun {0} () (_ FloatingPoint {1} {2}) {3})".format(args[0],
                                                                         args[1][0],
                                                                         args[1][1],
                                                                         args[2]))
        return args[0]

    ###################
    # STANDARD VALUES #
    ###################

    def make_floating_point(self, sign_bv, exp_bv, sig_bv, fp_fmt):
        """(fp sign exp sig)"""
        if len(sign_bv) != 3 or \
                len(exp_bv) != (fp_fmt[0] + 2) or \
                len(sig_bv) != (fp_fmt[1] + 1):
            raise ValueError("Incorrect arguments or fp_fmt.")
        for arg in (sign_bv, exp_bv, sig_bv):
            if not re.match(r"^#b[0|1]+$", arg):
                raise ValueError("The argument is not a Bit-Vector.")
        return "(fp {0} {1} {2})".format(sign_bv, exp_bv, sig_bv)

    def make_max_fp(self, fp_fmt):
        """(fp #b0 #b1...10 #b1...1)"""
        return "(fp #b0 #b{0}0 #b{1})".format("1" * (fp_fmt[0] - 1),
                                              "1" * (fp_fmt[1] - 1))

    def make_min_fp(self, fp_fmt):
        """(fp #b1 #b1...10 #b1...1)"""
        return "(fp #b1 #b{0}0 #b{1})".format("1" * (fp_fmt[0] - 1),
                                              "1" * (fp_fmt[1] - 1))

    def make_plus_inf(self, fp_fmt):
        """(_ +oo ebits sbits)"""
        return "(_ +oo {0} {1})".format(*fp_fmt)

    def make_minus_inf(self, fp_fmt):
        """(_ -oo ebits sbits)"""
        return "(_ -oo {0} {1})".format(*fp_fmt)

    def make_nan(self, fp_fmt):
        """(_ NaN ebits sbits)"""
        return "(_ NaN {0} {1})".format(*fp_fmt)

    def make_plus_zero(self, fp_fmt):
        """(fp #b0 #b0...0 #b0...0)"""
        return "(fp #b0 #b{0} #b{1})".format("0" * fp_fmt[0],
                                             "0" * (fp_fmt[1] - 1))

    def make_minus_zero(self, fp_fmt):
        """(fp #b1 #b0...0 #b0...0)"""
        return "(fp #b1 #b{0} #b{1})".format("0" * fp_fmt[0],
                                             "0" * (fp_fmt[1] - 1))


    ########################
    # CONVERSION OPERATORS #
    ########################

    def make_bv_to_fp(self, bv_number, fp_fmt):
        """(fp sign exp sig)"""
        if len(bv_number) != (fp_fmt[0] + fp_fmt[1] + 2):
            raise ValueError("Incorrect arguments or fp_fmt.")
        sign = bv_number[0:3]
        exp = "#b{0}".format(bv_number[3:3+fp_fmt[0]])
        sig = "#b{0}".format(bv_number[3+fp_fmt[0]:])
        return self.make_floating_point(sign, exp, sig, fp_fmt)


    #############
    # OPERATORS #
    #############

    def make_fp_abs(self, *args):
        """; absolute value
        (fp.abs (_ FloatingPoint ebits sbits))"""
        return "(fp.abs {0})".format(*args)

    def make_fp_neg(self, *args):
        """; negation (no rounding needed)
        (fp.neg (_ FloatingPoint ebits sbits))"""
        return "(fp.neg {0} {1})".format(*args)

    def make_fp_add(self, *args):
        """; addition
        (fp.add RoundingMode
                (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.add {0} {1} {2})".format(*args)

    def make_fp_sub(self, *args):
        """; subtraction
        (fp.sub RoundingMode
                (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.sub {0} {1} {2})".format(*args)

    def make_fp_mul(self, *args):
        """; multiplication
        (fp.mul RoundingMode
                (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.mul {0} {1} {2})".format(*args)

    def make_fp_div(self, *args):
        """; division
        (fp.div RoundingMode
                (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.div {0} {1} {2})".format(*args)

    def make_fp_fma(self, *args):
        """; fused multiplication and addition; (x * y) + z
        (fp.fma RoundingMode
                (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.fma {0} {1} {2} {3})".format(*args)

    def make_fp_sqrt(self, *args):
        """; square root
        (fp.sqrt RoundingMode
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.sqrt {0} {1})".format(*args)

    def make_fp_rem(self, *args):
        """; remainder: x - y * n, where n in Z is nearest to x/y
        (fp.rem (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.rem {0} {1})".format(*args)

    def make_fp_round_to_integral(self, *args):
        """; rounding to integral
        (fp.roundToIntegral RoundingMode
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.roundToIntegral {0})".format(*args)

    def make_fp_min(self, *args):
        """; minimum
        (fp.min (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.min {0} {1})".format(*args)

    def make_fp_max(self, *args):
        """; maximum
        (fp.max (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.max {0} {1})".format(*args)


    ########################
    # COMPARISON OPERATORS #
    ########################

    def make_fp_leq(self, *args):
        """; fp.leq -- evaluates to false if either argument is NaN
        (fp.leq (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.leq {0} {1})".format(*args)

    def make_fp_lt(self, *args):
        """; fp.lt -- evaluates to false if either argument is NaN
        (fp.lt (_ FloatingPoint ebits sbits)
               (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.lt {0} {1})".format(*args)

    def make_fp_geq(self, *args):
        """; fp.geq -- evaluates to false if either argument is NaN
        (fp.geq (_ FloatingPoint ebits sbits)
                (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.geq {0} {1})".format(*args)

    def make_fp_gt(self, *args):
        """; fp.gt -- evaluates to false if either argument is NaN
        (fp.gt (_ FloatingPoint ebits sbits)
               (_ FloatingPoint ebits sbits)
        )"""
        return "(fp.gt {0} {1})".format(*args)

    def make_fp_eq(self, *args):
        """; fp.eq -- evaluates to false if either argument is NaN
        (fp.eq (_ FloatingPoint ebits sbits)
               (_ FloatingPoint ebits sbits)
        )

        ; This is IEEE 754-2008 equality (as opposed to SMT-LIB =)
        ; (fp.eq x y) evaluates to true if x evaluates to -zero
        ; and y to +zero, or vice versa.
        """
        return "(fp.eq {0} {1})".format(*args)

    #############################
    # CLASSIFICATION OF NUMBERS #
    #############################

    def make_is_normal(self, *args):
        """(fp.isNormal (_ FloatingPoint ebits sbits))"""
        return "(fp.isNormal {0})".format(*args)

    def make_is_subnormal(self, *args):
        """(fp.isSubnormal (_ FloatingPoint ebits sbits))"""
        return "(fp.isSubnormal {0})".format(*args)

    def make_is_zero(self, *args):
        """(fp.isZero (_ FloatingPoint ebits sbits))"""
        return "(fp.isZero {0})".format(*args)

    def make_is_infinite(self, *args):
        """(fp.isInfinite (_ FloatingPoint ebits sbits))"""
        return "(fp.isInfinite {0})".format(*args)

    def make_is_nan(self, *args):
        """(fp.isNaN (_ FloatingPoint ebits sbits))"""
        return "(fp.isNaN {0})".format(*args)

    def make_is_negative(self, *args):
        """(fp.isNegative (_ FloatingPoint ebits sbits))"""
        return "(fp.isNegative {0})".format(*args)

    def make_is_positive(self, *args):
        """(fp.isPositive (_ FloatingPoint ebits sbits))"""
        return "(fp.isPositive {0})".format(*args)


def main():
    """A Test Function for class Environment"""

    env = Environment()

    fmt = env.make_float16_fp_fmt()

    x_var = env.declare_fp_var("x", fmt)
    y_var = env.declare_fp_var("y", fmt)
    z_var = env.declare_fp_var("z", fmt)

    add = env.make_fp_add(Environment.RoundingMode.RNE, x_var, y_var)
    env.assert_formula(env.make_fp_eq(z_var, add))

    zero = env.make_plus_zero(fmt)

    lower = env.make_floating_point("#b1", "#b10101", "#b0011001110", fmt)

    upper = env.make_bv_to_fp("#b0101010011001110", fmt)

    env.assert_formula(env.make_fp_leq(lower, x_var))
    env.assert_formula(env.make_fp_leq(x_var, upper))
    env.assert_formula(env.make_fp_leq(zero, y_var))
    env.assert_formula(env.make_fp_leq(y_var, upper))

    env.minimize(z_var)
    env.check_sat()
    env.get_model()

if __name__ == "__main__":
    main()
