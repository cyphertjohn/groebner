type var_power = Exp of string * int

type monic_mon = Prod of var_power list

type coef = Coef of float

type monomial = coef * monic_mon

type polynomial = Sum of monomial list