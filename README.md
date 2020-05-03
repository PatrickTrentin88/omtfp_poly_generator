# DESCRIPTION

Generates simple OMT(FP) problems finding the maximum relative difference
between the value returned by two FP functions when given the same inputs.

# INSTALLATION

To install the scripts, add the current directory
to the `PATH` environment variable:

    export PATH=$PATH:.../omtfp_poly_generator

To make these changes permanent, please consider
editing the `~/.bashrc` file.

# USAGE

    usage: formula_generator.py [-h] [--smt2 <file>.smt2] [--degree DEGREE]
                                [--format ebits sbits | --float16 | --float32 | --float64 | --float128]
    
    A poly-problem generator for OMT.
    
    optional arguments:
      -h, --help            show this help message and exit
    
    Main Options:
      --smt2 <file>.smt2    Filename for the generated SMT-LIB output
      --degree DEGREE       The degree of the polynome
      --format ebits sbits  Sets the required Floating-Point format
      --float16             Use the Float16 format
      --float32             Use the Float32 format
      --float64             Use the Float64 format
      --float128            Use the Float128 format

# EXAMPLES

## Example #01:

Creating a simple problem with Float16 and a polynome of degree 3.

    ~$ ./formula_generator.py --float16 --degree 3
    (set-option :config opt.verbose=true)
    ; x definition
    (declare-fun x () (_ FloatingPoint 5 11))
    (define-fun min_fp () (_ FloatingPoint 5 11) (fp #b1 #b11110 #b1111111111))
    (define-fun max_fp () (_ FloatingPoint 5 11) (fp #b0 #b11110 #b1111111111))
    (assert (fp.leq min_fp x))
    (assert (fp.leq x max_fp))
    (define-fun a_0 () (_ FloatingPoint 5 11) (fp #b0 #b10000 #b1111111110))
    (define-fun a_1 () (_ FloatingPoint 5 11) (fp #b0 #b01011 #b0111111111))
    (define-fun a_2 () (_ FloatingPoint 5 11) (fp #b0 #b00110 #b0011101010))
    ; f(x) definition
    (define-fun x_2 () (_ FloatingPoint 5 11) (fp.mul RNE x x))
    (define-fun fx_MUL_1 () (_ FloatingPoint 5 11) (fp.mul RNE a_1 x))
    (define-fun fx_MUL_2 () (_ FloatingPoint 5 11) (fp.mul RNE a_2 x_2))
    (define-fun fx_SUM_1 () (_ FloatingPoint 5 11) (fp.add RNE a_0 fx_MUL_1))
    (define-fun fx_SUM_2 () (_ FloatingPoint 5 11) (fp.add RNE fx_SUM_1 fx_MUL_2))
    (define-fun fx () (_ FloatingPoint 5 11) fx_SUM_2)
    ; g(x) definition
    (define-fun gx_MUL_2 () (_ FloatingPoint 5 11) (fp.mul RNE x a_2))
    (define-fun gx_SUM_2 () (_ FloatingPoint 5 11) (fp.add RNE a_1 gx_MUL_2))
    (define-fun gx_MUL_1 () (_ FloatingPoint 5 11) (fp.mul RNE x gx_SUM_2))
    (define-fun gx_SUM_1 () (_ FloatingPoint 5 11) (fp.add RNE a_0 gx_MUL_1))
    (define-fun gx () (_ FloatingPoint 5 11) gx_SUM_1)
    ; goal definition
    (define-fun abs_fx () (_ FloatingPoint 5 11) (fp.abs fx))
    (define-fun abs_gx () (_ FloatingPoint 5 11) (fp.abs gx))
    (define-fun max () (_ FloatingPoint 5 11) (fp.max abs_fx abs_gx))
    (define-fun sub () (_ FloatingPoint 5 11) (fp.sub RNE fx gx))
    (define-fun abs_sub () (_ FloatingPoint 5 11) (fp.abs sub))
    (declare-fun eps () (_ FloatingPoint 5 11))
    (define-fun eps_mul_max () (_ FloatingPoint 5 11) (fp.mul RNE eps max))
    (assert (fp.gt abs_sub eps_mul_max))
    (maximize eps)
    (check-sat)
    (get-objectives)
    (get-model)


## Example #02:

Creating and solving a simple problem with Float16 and a polynome of degree 3.

    ~$ ./formula_generator.py --float16 --degree 3 --smt2 formula.smt2
    ~$ time optimathsat formula.smt2
    # obj(.cost0) := eps
    # obj(.cost0) - search start: [ (_ NaN 5 11), (_ +oo 5 11) ]
    # obj(.cost0) -  new: (fp #b1 #b10110 #b1100101110)
    # obj(.cost0) -  update lower: [ (fp #b1 #b10110 #b1100101110), (_ +oo 5 11) ]
    # obj(.cost0) -  new: (fp #b0 #b00000 #b0000001000)
    # obj(.cost0) -  update lower: [ (fp #b0 #b00000 #b0000001000), (_ +oo 5 11) ]
    # obj(.cost0) -  new: (fp #b0 #b00101 #b0000000000)
    # obj(.cost0) -  update lower: [ (fp #b0 #b00101 #b0000000000), (_ +oo 5 11) ]
    # obj(.cost0) -  new: (fp #b0 #b00110 #b0000000000)
    # obj(.cost0) -  update lower: [ (fp #b0 #b00110 #b0000000000), (_ +oo 5 11) ]
    # obj(.cost0) -  new: (fp #b0 #b00110 #b0000001010)
    # obj(.cost0) -  update lower: [ (fp #b0 #b00110 #b0000001010), (_ +oo 5 11) ]
    # obj(.cost0) -  new: (fp #b0 #b00110 #b0000001011)
    # obj(.cost0) -  update lower: [ (fp #b0 #b00110 #b0000001011), (_ +oo 5 11) ]
    # obj(.cost0) - search end: sat_optimal
    # obj(.cost0) -  update upper: [ (fp #b0 #b00110 #b0000001011), (fp #b0 #b00110 #b0000001011) ]
    ; OFPBS Stats:
    ; SMT Calls: 16
    ; SAT Calls: 6
    ; UNSAT Calls: 10
    
    sat
    
    (objectives
     (eps (fp #b0 #b00110 #b0000001011))
    )
    ( (x (fp #b1 #b10101 #b0111000101))
      (eps (fp #b0 #b00110 #b0000001011)) )
    
    real    0m47.407s
    user    0m47.355s
    sys     0m0.052s


# [OptiMathSAT](http://optimathsat.disi.unitn.it/)

These are the relevant options for [OptiMathSAT](http://optimathsat.disi.unitn.it/)
when dealing with OMT(FP) problems.

    Theory options:
     -theory.fp.mode=INT
              Select which FP solver to use. Possible values are:
              - 0 : BV encoding with lazy bit-blasting
              - 1 : BV encoding with eager bit-blasting
              - 2 : ACDCL with interval domain.
     -theory.fp.bv_combination_enabled=BOOL
              If true, enable support for theory combination between FP and BV.

    Optimization search options:
     -opt.abort_interval=FLOAT
              If greater than zero, an objective is no longer actively optimized as 
              soon as the current search interval size is smaller than the given 
              value. Applies to all objective functions. (default: 0) 
     -opt.bin.max_consecutive=INT
              Sets the maximum number (> 0) of consecutive binary search steps 
              before a linear search step is performed for LAR/LIA objectives. 
              (default: 1) 
     -opt.bin.pivot_position=FLOAT
              Sets the position of the pivoting cut in binary search. Requires a 
              value in the interval ]0, 1] interval. When minimizing, a value 
              smaller than 0.5 results in a pivot closer to the lower bound than 
              the upper bound. Dual for maximization. (default: 0.5) 
     -opt.strategy=STR
              Sets the optimization search strategy: 
               - lin : linear search
               - bin : binary search (default)
               - ada : adaptive search
              A lower bound is required to minimize an objective with bin/ada 
              search strategy. Dual for maximization. 
    
    Optimization theory options:
     -opt.theory.fp.branch_preference=BOOL
              If true, it sets a branching preference on the FP objective. 
              (default: false) 
     -opt.theory.fp.engine=STR
              Sets the solving engine for dealing FP objectives:
               - omt    : standard OMT techniques
               - ofpbs  : FP optimization with binary search over the bits (default)
               - ofpbls : FP optimization with binary search with linear cuts
     -opt.theory.fp.polarity=BOOL
              If true, sets the initial polarity of any FP objective towards the 
              maximum gain direction. (default: true) 
     -opt.theory.fp.safe_bits_only=BOOL
              If true, polarity and branch_preference are only set for those bits 
              for which the maximum gain direction is certain. (default: true) 


# Contributors

This project is authored by [Patrick Trentin](http://www.patricktrentin.com) (<patrick.trentin.88@gmail.com>).


