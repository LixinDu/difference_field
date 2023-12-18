######################################################################################
## Copyright (c) December 2023, JKU. All rights reserved.
## Author: Lixin Du <lx.du@hotmail.com>
## Modified on December 7, 2023
######################################################################################


######################################################################################
## Part 1: spread computation of two multivariate polynomials.
######################################################################################

def make_in_multi_fraction_field(f, x, *, var_name = False, polynomial_ring = False):
    """
    change the parent of a rational function to a multivariate rational function field. 
    For example, from QQ(x1)(x2) to QQ(x1,x2).

    OPTIONAL::

    If polynomial_ring = True, change the parent of a polynomial to a multivariate polynomial ring. 
    For example, from QQ(x1)[x2] to QQ[x1,x2].
    

    EXAMPLE::

        sage: R.<x1> =  PolynomialRing(QQ)
        sage: T.<x2> = R.fraction_field()['x2']
        sage: x1,x2 = R.gen(),T.gen()
        sage: f = x1^2 + x2
        sage: f.parent()
        Univariate Polynomial Ring in x2 over Fraction Field of Univariate Polynomial Ring in x1 over Rational Field
        sage: g = make_in_multi_fraction_field(f,[x1,x2], polynomial_ring = True);g
        x1^2 + x2
        sage: g.parent()
        Multivariate Polynomial Ring in x1, x2 over Rational Field
    """
    C = f.base_ring()
    ## Note: the generator of QQ(sqrt(5)) is sqrt(5). The generator of QQ is 1.
    while C.gen() in x: 
        C = C.base_ring()

    var_names = ['{}'.format(u) for u in x]
    
    MultiPolyRing = PolynomialRing(C, var_names)
    MultiPolyRing.inject_variables(verbose=False)
    xx = list(MultiPolyRing.gens())
    MultiFractionField = MultiPolyRing.fraction_field()
    
    ## SR is the symbolic ring, the following line may not work in QQ(sqrt(5))
    # g = MultiFractionField(SR(f))
    g = MultiFractionField(f)

    if polynomial_ring:
        g = g.numerator()

    if var_name:
        return g, xx
    else:
        return g


def tau(f,x,a,k):
    """
    substitute x by x = (a^k)*x in the expression f
    
    INPUT::
    
        "f", a rational function
        "x", a list of varialbes
        "a", a list of numbers    
        "k", an integer
        
    OUTPUT::
    
        "g", a rational function such that 
                g(x_1, ..., x_n) = f(a_1^k*x_1, ..., a_n^k*x_n)
         where x = [x_1, ..., x_n], a = [a_1, ..., a_n].
         
    EXAMPLES::
    
        sage: R.<x1,x2> = PolynomialRing(QQ,'x1,x2')
        sage: R.fraction_field()
        sage: tau(1/(x1+x2+1),[x1,x2],[2,3],2)
        1/(4*x1 + 9*x2 + 1)
    
    """
    if list(f.parent().gens()) != x:
        # if the variables of the polynomial ring or the rational fraction field containing f 
        # does not match x, then construct a rational function field in x with the same base ring
        # For example, if f in QQ(x1)(x2), then we view f as in QQ(x1,x2)
        g, xx = make_in_multi_fraction_field(f,x, var_name = True)

    else:
        g = f
        xx = list(f.parent().gens())
    
    return g.subs({xx[i]: (a[i] ** k) * xx[i] for i in range(len(a))})

def sigma(f,x,a):
    """
    substitute x by x = a*x in the expression f

    INPUT::
    
        "f", a rational function
        "x", a list of varialbes
        "a", a list of numbers    

        
    OUTPUT::
    
        "g", a rational function such that 
                g(x_1, ..., x_n) = f(a_1*x_1, ..., a_n*x_n)
         where x = [x_1, ..., x_n], a = [a_1, ..., a_n].
    """
    return tau(f, x, a, 1)


def delta(f,x,a,c):
    """
    substitute x by x = a*x in the expression f

    INPUT::
    
        "f", a rational function
        "x", a list of varialbes
        "a", a list of numbers    

        
    OUTPUT::
    
        "g", a rational function such that 
                g(x_1, ..., x_n) = f(a_1*x_1, ..., a_n*x_n) - f(x_1, ..., x_n)
         where x = [x_1, ..., x_n], a = [a_1, ..., a_n].
    """
    return c*sigma(f, x, a) - f
    

def my_isolve(A,b):
    """
    compute one integer solution of A*x = b if there exists
    
    INPUT::
    
        "A", a matrix in Z^{n*m}
        "b", a vector in Z^n
    
    OUTPUT::
 
        Let x be a vector in Z^m such that A*x = b; 
        return "x" if there is such an integer solution; otherwise return "[]"
    
    EXAMPLES::
    
        sage: my_isolve(matrix(ZZ,2,2,[[2,5],[3,5]]), vector([3,2]))
        (-1, 1)
        sage: my_isolve(matrix(ZZ,2,1,[1,2]), vector([2,4]))
        (2)
        sage: my_isolve(matrix(ZZ,1,3,[2,3,5]), vector([1]))
        (0, 2, -1)
        sage: my_isolve(matrix(ZZ,1,2,[2,2]), vector([1]))
        []
    """
    ## Compute the smith normal form D of A such that D = U*A*V
    D,U,V = A.smith_form()
    
    ## Then A*x = b is equivalent to D*V^{-1} x = U*b. Let c = U*b and solve D*y = c
    c = U*b
    
    ## if the rank of the augmented matrix is larger, there is no solution for x
    if D.rank() != D.augment(c).rank():
        return []
    
    y = []
    m = A.ncols()
    s = len(D.diagonal())
    for i in range(s):
        d_i, c_i = D.diagonal()[i], c[i]
        
        # choose a special solution with free varaibles being zero
        if d_i == 0:
            y.append(0) 
        elif c_i%d_i == 0:
            y.append(c_i/d_i)
            
        # if c_i is not divisble by d_i, there is no integer solution for x
        else:
            return []
            break
    
    for i in range(s,m):
        y.append(0)
        
    ## x = V*y
    return V*vector(y)


def integer_expression(a,numbers):
    """
    determine whether an algebraic number is the product of the other algebraic numbers and their inverses.
    
    INPUT::
    
        "a", an aglebraic number
        "numbers", a list of algebraic numbers
    
    OUTPUT::
    
        Let x = [x_1, ..., x_n]. If there exists a list of integers z = [z_1, ..., z_n] such that 
              a = x_1^{z_1} * ... * x_n^{z_n},
        return "z", which is one such a solution; otherwise return "[]".
    
    EXAMPLES:
    
        sage: integer_expression(4,[1/2, 2])
        [0,2]
        sage: integer_expression(5,[1/2, 2])
        []
        sage: integer_expression(2,[4, 3])
        []
        sage: integer_expression(4,[3, 5])
        []
    """
    L = numbers.copy()
    L.append(a)
    relation = IntegerRelations.integer_relations(L) 
    if relation.nrows() == 0:
        return []
    A = relation[:,-1].transpose() # take the last column of A
    b = vector([-1])

    ## find one integer solution x of the linear system A x = b if it exists
    sol = my_isolve(A,b) 
    if sol == []:
        return []
    else:
        return list(relation[:, 0: -1].transpose()*sol) 



def spread_local(v,u,p_u,q_u,x,a,*,relation = None):
    """
    when supp(p)=supp(q) and |supp(p)|= 2, compute the spread of p and q, 
    where p = v + u*p_u, q = v + u*q_u with u and v being monomials and p_u, q_u in the coefficient field.
    
    EXAMPLES::
        
        ## p = x1 + x2, q = x1 - x2, a = [1, -1], spread(p,q) = 1 + 2*ZZ
        sage: R.<x1,x2> = PolynomialRing(QQbar, order = 'negdeglex') 
        sage: spread_local(x1,x2,1,-1,[x1,x2],[1,-1])
        [1,2]
        sage: spread_local(x1,x2,1,-4/3,[x1,x2],[4,3])
        []
        sage: rel=IntegerRelations.integer_relations([1,-1]);
        sage: spread_local(x1,x2,1,-1,[x1,x2],[1,-1],relation = rel)
        [1,2]
        sage: spread_local(x1,x2,1,4,[x1,x2],[2,2])
        []
    """
    n = len(a)
    if n == 1:
        v_index = [v.exponents()[0]]
        u_index = [u.exponents()[0]]
    else:
        v_index = v.exponents()[0]
        u_index = u.exponents()[0]
    
    b = integer_expression(p_u/q_u, a)
    if b == []:
        return []
    else:
        b = vector(b)
    if relation == None:
        relation = IntegerRelations.integer_relations(a) # which is a matrix over ZZ
    A0 = vector(v_index)-vector(u_index)
    A = relation.insert_row(0,A0).transpose()

    ## find one integer solution x of the linear system A x = b if it exists
    sol = my_isolve(A,b) 
    if sol == []:
        return []
    else:
        k = sol[0]
   
    ## find the null space of A over the ring of integers
    #### TODO: output the solution x of A x = 0 when we solve A x = b?
    kernel = A.right_kernel() 
    if kernel.rank() == 0:
        j = 0
    else:
        basis = kernel.basis_matrix()
        j = gcd(list(basis.column(0)))
    
    ## take the smallest non-negative solution for k if j is not zero
    if j != 0:
        k = k%j
    ## spread = k + j*ZZ
    return [k,j]


def my_intersection(L1, L2):
    """
    compute the interesction of two subsets k1 + j1*ZZ and k2 + j2*ZZ
    
    INPUT::
    
        "L1", either L1 = [] or L1 = [k1, j1], a list of two integrs
        "L2", either L2 = [] or L2 = [k2, j2], a list of two integrs
    
    OUTPUT::
    
        Let k, j be two integers such that k + j*ZZ = the intetersection of (k1 + j1*ZZ) and (k2 + j2*ZZ)
        return "[k, j]" if the intersection is nonempty
        otherwise, return "[]"
    
    EXAMPLES::
    
        sage: my_intersection([2,3],[3,5])
        [8,15]
        sage: my_intersection([2,0],[3,5])
        []
        sage: my_intersection([2,0],[0,1])
        [2, 0]
    """
    #### find the intersection of L1 and L2 by extended Euclidean algorithm or solving a linear diophantine equation?
    if L1 == [] or L2 == []:
        return []
    
    k1, j1 = L1[0], L1[1]
    k2, j2 = L2[0], L2[1]
    
    if j1 == 0 and j2 == 0:
        return [k1, 0] if k1==k2 else []

    ## k1 + j1*ZZ = k1 is a single point
    elif j1 == 0 and j2 != 0:  
        return [k1, 0] if k2 == (k1%j2) else [] # check if k1 is in k2 + j2*ZZ


    ## k2 + j2*ZZ = k2 is a single point
    elif j1 != 0 and j2 == 0: 
        return [k2, 0] if k1 == k2%j1 else []  # check if k2 is in k1 + j1*ZZ

    else: # j1 != 0 and j2 != 0:
        # compute k such that k = k1 mod j1 and k = k2 mod j2 by Chinese remainder theorem
        try:
            k = crt([k1, k2], [j1, j2])
        except ValueError: # there is no such an integer k
            return []
        j = lcm(j1, j2)
        return [k, j]
    

def spread(p,q,x,a,*,constant = False,relation = None):
    """
    determines whether two polynomials p,q are shift equivalent or not with respect to tau, 
    i.e., whether there exists an integer i such that tau^i(p) = c*q for some nonzero constant c, 
    where tau(p(x)) = p(a*x). Here a*x = [a_1*x_1, ..., a_n*x_n] if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].
    
    INPUT::
    
        "p", "q", two polynomials in QQbar[x]
        "x", a list of variables
        "a", a list of numbers in QQbar
    
    OUTPUT::
    
       If p and q are shift equivalent with respect to tau, return "[k, j]" such that 
                    {k + j*m | m is an integer} 
            forms the solution set {i | i is an integer such that tau^i(p) = c*q for some nonzero constant c};
       otherwise, return "[]".
       
    OPTIONAL::
    
       If constant = True, return "[k, j], [c_1, c_2]" such that tau^k(p) = c_1 * q and tau^j(p) = c2 * p
       If constant = False, return "[k, j]".
    
    EXAMPLES::
    
        sage: R.<x1,x2> = PolynomialRing(QQbar, order = 'negdeglex');
        sage: spread(x1 + x2, 4*(2*x1 + 3*x2), [x1, x2], [2,3])
        [1, 0]
        sage: spread(x1+x2+x2^2, x1-x2+x2^2, [x1,x2], [1,-1])
        [1, 2]
        sage: rel = IntegerRelations.integer_relations([2,-1])
        sage: spread(x1 + x2, 4*(2^3*x1 + (-1)^3*x2), [x1, x2], [2,-1], constant = True,relation = rel)
        ([3, 0], [1/4, 1])
        
    """
    #### compare the support of p and q
    supp_p, coeff_p = p.monomials(), p.coefficients()
    supp_q, coeff_q = q.monomials(), q.coefficients()

    if supp_p != supp_q:
        return []
    else:
        if len(supp_p) == 0: ## p = q = 0
            if constant:
                return [0,1], [1,1]
            else:
                return [0,1]
    
    #### consider the case that supp_p = supp_q
    
    ## obtain the index of the leading monomial of p
    n = len(a)
    if n == 1:
        # Note: in the univariate case, the monomials and coefficients are not consistent.
        # For example, when p = x1 + 3*x1^2, p.monomials() = [x1^3, x1], p.coefficients() = [1,3] 
        supp_p.reverse()
        supp_q.reverse()
        lm = supp_p[0]
        lm_index = [lm.exponents()[0]]
    else:
        lm = supp_p[0]
        lm_index = lm.exponents()[0]

    ## initialize some data about leading monomials
    k = 0
    j = 1                     
    c1 = 1 # c1 = a^(k*lm_index) = a^0 = 1
    c2 = prod([a[i]**lm_index[i] for i in range(n)])  # c2 = a^(j*lm_index) = a^lm_index
    
    ## prepare the input when supp_q = supp_p contains only one element
    if len(supp_p) == 1: 
        if constant:
            return [0,1], [c1,c2]
        else:
            return [0,1]

    ## consider the case that supp_q = supp_p contains at least two elements
    T = supp_p
    lc_p = coeff_p[0]
    lc_q = coeff_q[0]

    if relation == None:
        relation = IntegerRelations.integer_relations(a)
    
    for (u, p_u, q_u) in zip(T[1:], coeff_p[1:], coeff_q[1:]):
        #u = T.pop(0) # remove and return the first element (index = 0) of T
        p_u = p_u/lc_p # coefficient of the monomial u in p_monic
        q_u = q_u/lc_q # coefficient of the monomial u in q_monic
        
        ## consider the spread of polynoimals p_ = lm + p_u*u and q_ = lm + q_u*u, which contains two monomials
        p_ = lm + p_u*u
        q_ = lm + q_u*u

        ## if spread(p_, q_) == k + j*ZZ, i.e. tau^k(p_) == c*q_ and tau^j(p) = c*p, go to the next term in T 
        ## else, we need to update k, j, c
        if not (tau(p_,x,a,k) == c1*q_ and tau(p_,x,a,j) == c2*p_):
            
            # if |spread(p, q)| <= 1 and k is not in Spread(p,q); then spread = []
            if tau(p_,x,a,k) != c1*q_ and j == 0: 
                return []
            
            # compute spread(p_,q_)
            spread_temp = spread_local(lm,u,p_u,q_u,x,a,relation = relation)
            spread_interesct = my_intersection([k,j],spread_temp)
            
            if spread_interesct == []:
                return []
            else:
                k, j = spread_interesct[0], spread_interesct[1]
                
                # tau^k(p_monic) = c1 * q_monic; tau^j(p_monic) = c2 * p_monic
                c1 = prod([a[i]**(k*lm_index[i]) for i in range(n)])
                c2 = prod([a[i]**(j*lm_index[i]) for i in range(n)])
    
    if constant:
        ## tau^k(p) = c1 * q; tau^j(p) = c2 * p
        c1 = c1*lc_p/lc_q
        return [k,j],[c1,c2]   
    else:  
        return [k,j]

def isotropy_group(p,x,a,*,constant = False,relation = None):
    """ 
    compute the isotropy group of a given polynomials with respect to tau, i.e., find all 
    integer k such that tau^k(p) = c*p for some nonzero constant c, where tau(p(x)) = p(a*x). 
    Here a*x = [a_1*x_1, ..., a_n*x_n] if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].
    
    INPUT::
    
        "p", a polynomial in QQbar[x]
        "x", a list of variables
        "a", a list of numbers in QQbar
    
    OUTPUT::
    
        "k", an integer such that {k*m | m is an integer} forms the solution set 
            {i | i is an integer such that tau^i(p) = c*p for some nonzero constant c};
       
    OPTIONAL::
    
       If constant = True, return "[k, j], [c_1, c_2]" such that tau^k(p) = c_1 * q and tau^j(p) = c2 * p
       If constant = False, return "[k, j]".
    
    EXAMPLES::
    
        sage: R.<x1,x2> = PolynomialRing(QQbar);
        sage: spread(x1 + x2, 4*(2*x1 + 3*x2), [x1, x2], [2,3])
        [1, 0]
        sage: spread(x1+x2+x2^2, x1-x2+x2^2, [x1,x2], [1,-1])
    """
    sol = spread(p,p,x,a,constant = constant,relation = relation)
    if sol == []:
        return []
    else:
        if constant:
            return sol[0][1],sol[1][1]
        else:
            return sol[1]


######################################################################################
## Part 2: obital partial fraction decompositions of multivariate rational functions
######################################################################################

def orbital_factorization(p, x, a,*, group = False, relation = None):
    """
    compute the irreducible factorization of a polynomial and group its irreducible factors into the same 
    shift equivalent classes with respect to tau, where tau(p(x_1, ..., x_n)) = p(a_1*x_1, ..., a_n*x_n)
    if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].
    
    INPUT::
    
        "p", a multivariate polynomial over a subfield of QQbar
        "x", a list of variables
        "a", a list of numbers 
        
    OUTPUT::
         
        "L", a list
        
                 [c, {d_1: [[d_11, k_11, e_11], [d_12, k_12, e_12], ...], d_2: [...], ...}],
                 
            representing an orbital irreducible factorization of p w.r.t. x, where c is a constant,
            d_ij = tau^{k_ij}(d_i) are irreducible polynoimals, k_ij in ZZ, e_ij is the multiplicity 
            of d_ij in p, and the d_i's are in distinct orbits, i.e., tau^k(d_i) != d_j for all k in 
            ZZ and i != j. 
            
            A factorization of p is as follows:
                 
                  p = c * tau^{k_11}(d_11)^{e_11} * tau^{k_12}(d_12)^{e_12}...
                  
    OPTIONAL::
        
        If group = True, return "L, Gp", where Gp = [[k_1, c_1], [k_2, c_2], ...] such that
        tau^{k_1} (p_1) = c_1 * p_1, tau^{k_2} (p_2) = c_2 * p_2, ...
        
        Possible options of "relation" are "None" and integer relation of a
    
    
    EXAMPLE::
        
        sage: R.<x1,x2> = PolynomialRing(QQ)
        sage: p = 4*expand((x1^2 + x2)*(4*x1^2+x2)*(x2+2)*(-x2+2))
        sage: orbital_factorization(p, [x1,x2], [2,-1])
        [-4,
         {x2 - 2: [[x2 - 2, 0, 1], [x2 + 2, 1, 1]],
          x1^2 + x2: [[x1^2 + x2, 0, 1]],
          4*x1^2 + x2: [[4*x1^2 + x2, 0, 1]]}]
        sage: rel = IntegerRelations.integer_relations([2,-1])
        sage: orbital_factorization(p, [x1,x2], [2,-1], group = True, relation = rel)
        ([-4,
          {x2 - 2: [[x2 - 2, 0, 1], [x2 + 2, 1, 1]],
           x1^2 + x2: [[x1^2 + x2, 0, 1]],
           4*x1^2 + x2: [[4*x1^2 + x2, 0, 1]]}],
          {x2 - 2: [2, 1], x1^2 + x2: [0, 1], 4*x1^2 + x2: [0, 1]})
    """

    if relation == None:
        relation = IntegerRelations.integer_relations(a)
    
    #### determine whether p is a constant polynomial or not
    if p.monomials() == [1]:
        if group:
            return [p,{}],{}
        else:
            return [p, {}]

    factors = p.factor()

    #### compute the constant in the factorization
    c = factors.unit()
    
    #### group together irreducible factors in the same shift-equivalence class
    orbital_dic = {}
    if group:
        group_dic = {}
        
    for d2, e2 in factors:
        flag = False
        for d1 in orbital_dic:
            sol = spread(d1, d2, x, a, constant=True, relation=relation)

            if sol != []:
                # d1 and d2 are shift equivalent; add d2 to the orbit represented by d1
                # tau^k(d1) = c1*d2; tau^j(d1) = c2 * d1
                k, j = sol[0][0], sol[0][1]
                c1, c2 = sol[1][0], sol[1][1]
                d2 = d2*c1
                c = c/(c1**e2)
                orbital_dic[d1].append([d2, k, e2])
                flag = True

        # create a new orbit represented by d2
        if flag == False:
            orbital_dic[d2] = [[d2, 0, e2]]
            if group:
                # TODO: if the orbit represented by d1 contains at least two elements, 
                # we may avoid computing isotropy_group?)
                sol = isotropy_group(d2, x, a, constant=True, relation=relation)
                j, c2 = sol[0], sol[1]
                group_dic[d2] = [j, c2]

    if group:
        return [c, orbital_dic], group_dic
    else:
        return [c, orbital_dic]


def from_list_to_polynomial(L,x,a):
    """
    convert a list representation of an orbital factorization to a polynomial

    INPUT::

        "L", a list
        
            [c, {d_1: [[d_11, k_11, e_11], [d_12, k_12, e_12], ...], d_2: [...], ...}],
                 
            representing an orbital irreducible factorization of p w.r.t. x.

    OUTPUT::

        "p", a polynomial such that p = c * tau^{k_11}(d_11)^{e_11} * tau^{k_12}(d_12)^{e_12}...
    """
    c = L[0]
    F = L[1]
    p = c
    for d,orbit in F.items():
        for d1, k1, e1 in orbit:
            if d1 != tau(d,x,a,k1):
                return False
            p = p*(d1**e1)
    return p


def make_main_variable(f, x, *, var_name = False, polynomial_ring = False):
    """
    change the parent of a rational function f to QQ(x_1,...,x_{n-1})(x_n), where x = [x_1, ..., x_n]. 
    For example, from QQ(x1,x2) to QQ(x1)(x2); or from QQ(x1,x2) to QQ(x1) if f is free of x2 and x = [x1]

    OPTIONAL::

    If polynomial_ring = True, change the parent of f to QQ(x_1,...,x_{n-1})[x_n].
    In this case, f should be a polynomial in x_n. 

    EXAMPLE::

        sage: R.<x1> =  PolynomialRing(QQ)
        sage: T.<x2> = R.fraction_field()['x2']
        sage: S = T.fraction_field()
        sage: x1,x2 = R.gen(),T.gen()
        sage: f = S(x1^2 + 1)
        sage: f.parent()
        Fraction Field of Univariate Polynomial Ring in x2 over Fraction Field of Univariate Polynomial Ring in x1 over Rational Field
        sage: g = make_main_variable(f,[x1,x2]);g
        x1^2 + 1
        sage: g.parent()
        Fraction Field of Univariate Polynomial Ring in x1 over Rational Field
    """
    C = f.base_ring()
    i = 0
    while C.gen() in x and i <= len(x):
        C = C.base_ring()
        i = i + 1

    var_names = ['{}'.format(u) for u in x[:-1]]
    var_main = '{}'.format(x[-1])
    
    if var_names == []:
        P = C
    else:
        P = PolynomialRing(C, var_names)
        P.inject_variables(verbose=False)

    T = P.fraction_field()[var_main]
    S = T.fraction_field()
   
    g = S(f)

    if polynomial_ring:
        g = g.numerator()
    
    if var_name:
        if var_names == []:
            xx = [T.gen()]
        else:
            xx = [*list(P.gens()),T.gen()]
        return g, xx
    else:
        return g


def my_denom(f, x):
    """compute the denominator of f, which is a polynomial in x and primitive with respect to x_n
       if x = [x_1, ..., x_n]
    
        INPUT::
    
        "f", a multivariate rational function over a subfield of QQbar
        "x_n", a main variable, which must be the last element in x
        "x", a list of variables

        OUTPUT::
        "q", the denominator of f, which is a multivariate polynomial in x and primitive w.r.t. x_n 
             such that q*f is a polynomial in x_n
        
        EXAMPLE::
    """
    self = make_in_multi_fraction_field(f, x)
    denom = make_main_variable(self.denominator(), x, polynomial_ring = True)

    #### compute the content of denom w.r.t. x_n
    c = gcd(denom.coefficients())
    return denom//c


def orbital_partial_fraction(f, x_n, x, a,*, group = False, relation = None):
    """
    compute the partial fraction decomposition of a rational function w.r.t. x_n and 
    group the irreducible factors of the denominator of f into the same shift equivalent 
    classes with respect to tau, where tau(p(x_1, ..., x_n)) = p(a_1*x_1, ..., a_n*x_n) 
    if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].
    
    INPUT:: 
    
        "f", a multivariate rational function over a subfield of QQbar
        "x_n", a main variable, which must be the last element in x
        "x", a list of variables and x = [x_1, ..., x_n]
        "a", a list of numbers 
        
    OUTPUT::
    
        "L", a list 
        
                [f_0, {d_1: [[k_11, a_11, e_11], [k_12, a_12, e_12], ...], d_2: [...], ...}]
                    
            representing an orbital irreducible partial fraction decomposition of f w.r.t. x1.
            where f_0 is a polynomial in x_n, d_i are irreducible polynoimals, k_ij, e_ij in ZZ, 
            a_ij's are polynomials in x_n with deg_{x_n}(a_ij) < deg_{x_n}(d_i^{e_ij}). Moreover, the d_i's
            are in disctinct orbits, i.e., tau^k(d_i) != d_j for all k in ZZ and i != j. 
                
            An orbital partial fraction decomposition of f is as follows:
                 
                f = f_0 + a_11/tau^{k_11}(d_1)^{e_11} + a_12/tau^{k_12}(d_1)^{e_12} + ...
             
    OPTIONAL::
    
        If group = True, return "L, Gp", where Gp = [[k_1, c_1], [k_2, c_2], ...] such that
        tau^{k_1} (d_1) = c_1 * d_1, tau^{k_2} (d_2) = c_2 * d_2, ...
        
    EXAMPLE::

        sage: R.<x1> =  PolynomialRing(QQ)
        sage: T.<x2> = R.fraction_field()['x2']
        sage: x1,x2 = R.gen(),T.gen()
        sage: S = T.fraction_field()
        sage: g = x2+x2^2/expand((x2^2 + x1)*(4*x2^2 + 2*x1)*(x1+2)*(-x1+2))
        sage: f = S(g)
        sage: orbital_partial_fraction(f, x2, [x1,x2], [2,2])
        [x2, {x2^2 + x1: [[0, -1/2/(x1^2 - 4), 1], [1, 1/(x1^2 - 4), 1]]}]
    """
    self = f

    #### obtain the denominator of f, which should be a polynomial in x and be primitive w.r.t. x_n
    denom = my_denom(self, x)
    num = make_main_variable(self*denom, x, polynomial_ring = True)
    whole, numer = num.quo_rem(denom)

    # change the parent of denom from a univariate polynomial ring in x1 to a multivariate ploynomial ring
    denom_poly, xx = make_in_multi_fraction_field(denom, x, var_name = True, polynomial_ring = True)

    if relation == None:
        relation = IntegerRelations.integer_relations(a)

    orbital_factors, group_dic = orbital_factorization(denom_poly, xx, a, group=True, relation = relation)
    orbital_factors = orbital_factors[1]

    if not self.parent().is_exact():
        # factors not grouped in this case
        all = {}
        for orbit in orbital_factors.values():
            for r, k, e in orbit:
                all[r[0]] = 0
        for orbit in orbital_factors.values():
            for r, k, e in orbit:
                all[r[0]] += r[1]
        orbital_factors = sorted(all.items())

    # TODO(robertwb): Should there be a category of univariate polynomials?
    from sage.rings.fraction_field_element import FractionFieldElement_1poly_field

    is_polynomial_over_field = isinstance(self, FractionFieldElement_1poly_field)

    running_total = 0
    parts_dic = {}
    for r1, orbit in orbital_factors.items():
        parts_dic[r1] = []
        for r, k, e in orbit:
            powers = [1]
            for ee in range(e):
                powers.append(powers[-1] * r)
            d = powers[e]
            # change the parent of d from a multivariate ploynomial ring to a univariate polynomial ring in x_n
            d = make_main_variable(d, x, polynomial_ring = True)
            denom_div_d = denom // d
            # We know the inverse exists as the two are relatively prime.
            n = ((numer % d) * denom_div_d.inverse_mod(d)) % d
            if not is_polynomial_over_field:
                running_total += n * denom_div_d
            # If the multiplicity is not one, further reduce.
            # if decompose_powers:
            #     r_parts = []
            #     for ee in range(e, 0, -1):
            #         n, n_part = n.quo_rem(r)
            #         if n_part:
            #             r_parts.append(n_part / powers[ee])
            #     parts.extend(reversed(r_parts))
            # else:
            #    parts.append(n / powers[e])
            parts_dic[r1].append([k, n, e])

    if not is_polynomial_over_field:
        # remainders not unique, need to re-compute whole to take into
        # account this freedom
        whole = (self*denom - running_total) // denom

    if group:
        return [whole, parts_dic], group_dic
    else:
        return [whole, parts_dic]   


def from_list_to_partial_fraction(L, x, a):
    """
    convert a list representation of an orbital partial fraction to an orbital partial fraction

    INPUT::

        "L", a list
        
            [f_0, {d_1: [[k_11, a_11, e_11], [k_12, a_12, e_12], ...], d_2: [...], ...}]
                    
            representing an orbital irreducible partial fraction decomposition of f w.r.t. x1.
        "x", a list of variables
        "a", a list of integers

    OUTPUT::

        "g", a rational function such that g = f_0 + a_11/tau^{k_11}(d_1)^{e_11} + a_12/tau^{k_12}(d_1)^{e_12} + ...
    """
    whole = L[0]
    F = L[1]
    parts = []
    for d,orbit in F.items():
        #orbits = []
        g = 0
        #d, xx = parent_from_frationfield_to_polyring(d, x, var_name = True)
        for k, n, e in orbit:
            dd = tau(d,x,a,k)**e
            g = g + n / dd
            #orbits.append(n /dd)
        parts.append(g)
        #parts.append(sum([n / tau(d,x,a,k)**e for k, n, e in orbit]))    
    
    return whole, parts

######################################################################################
## Part 3: obital reduction for multivariate rational functions
######################################################################################

def reduce_fraction(p, q, x, a, c, k):
    """
    decompose a rational function into a summable part and a remainder such that the denominator
    of the remainder belongs to the same orbit as the denominator of a given function.

    INPUT::

        "p",  a multivariate polynomial or rational function
        "q",  a multivariate polynomial or rational function
        "x",  a list of variables
        "a",  a list of nonzero numbers
        "c",  a nonzero number
        "k",  an integer

    OUTPUT::

        "[g, p1]", g, p1 are rational functions such that 
                        p/ tau(q) = c * tau(g) - g + p1/q
                where tau(p(x)) = p(a*x) and a*x = [a_1*x_1, ..., a_n*x_n] 
                if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].

    EXAMPLE::

        sage: R.<x1> =  PolynomialRing(QQ)
        sage: T.<x2> = R.fraction_field()['x2']
        sage: x1,x2 = R.gen(),T.gen()
        sage: p, q, x, a, c, k = 1/(x1^2 - 1), x1^2 + x2, [x1,x2], [2,2], 2, 1
        sage: reduce_fraction(p, q, x, a, c, k)
        [1/2/(1/4*x1^4 + 1/4*x1^2*x2 - x1^2 - x2), 1/2/(1/4*x1^2 - 1)]
    """
    if k >=0:
        g = add([c**(i-k)*tau(p, x ,a , i-k)/tau(q, x, a, i) for i in range(k)])
    else:
        g = - add([tau(p, x ,a , i)/tau(q, x, a, k+i) for i in range(-k)])
    p1 = c**(-k) * tau(p, x, a, -k)
    return [g, p1]


def reduce_one_orbit(d, orbit, x, a, c):
    """
    reduce one component in the orbital partial fraction to a simple fraction

    INPUT::

        "d",  a multivariate polynomial
        orbit,  a list = [[k_1, n_1, e_1], [k_2, n_2, e_2], ...] representing one orbit in the orbital 
                partial fraction decomposition
        "x",  a list of variables
        "a",  a list of nonzero numbers
        "c",  a nonzero number
    
    OUTPUT::

        "[g, r_list]", a list with r_list = [d, n, e] such that 

                            f = c * tau(g) - g + n/d^e

                    where f = n_1/ tau^{k_1}(d)^{e_1} + n_2/ tau^{k_2}(d)^{e_2}...
                    is the rational function corresponding to "d, orbit";
                    g is a rational function, n is a polynomial or rational function, e is an integer;
                    tau(g(x)) = g(a*x) and a*x = [a_1*x_1, ..., a_n*x_n] 
                    if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].
    
    REMARK::
        
        If the remainder represented by [d, n, e] is zero, i.e., n = 0, then we assign r = [].

    EXAMPLE::
        
        sage: R.<x1> =  PolynomialRing(QQ)
        sage: T.<x2> = R.fraction_field()['x2']
        sage: x1,x2 = R.gen(),T.gen()
        sage: S = T.fraction_field()
        sage: d, orbit, x, a, c = S(2*x2^2 + x1), [[0, S(1/2/(x1^2 - 4)), 1],[1, S(1/2*x2), 2]], [x1,x2], [2,2], 2
        sage: reduce_one_orbit(d, orbit, x, a, c)
        (1/8*x2/(4*x2^4 + 4*x1*x2^2 + x1^2),
         [2*x2^2 + x1, (1/(x1^2 - 4))*x2^2 + 1/8*x2 + 1/2*x1/(x1^2 - 4), 2])
    """
    g = 0
    r_orbit = []
    for k, n, e in orbit:
        g1, n1 = reduce_fraction(n, d**e, x, a, c, k)
        g = g + g1
        r_orbit.append([n1,e]) 
        
    ## compute the maximal multiplicity
    e = max([u[1] for u in r_orbit])

    ## collect numerators
    n = add([ n1*d**(e-e1) for n1, e1 in r_orbit])

    ## prepare the output
    if n == 0:
        r_list = []
    else:
        r_list = [d, n, e]
    
    return [g, r_list]


def reduction(L, x, a, c, *, group = None):
    """
    reduce each component in the orbital partial fraction to a simple fraction

    INPUT::

        "L",  a list {d_1: [[k_11, n_11, e_11], [k_12, n_12, e_12], ...], d_2: [...], ...}                
                representing an orbital irreducible partial fraction decomposition of f w.r.t. x1.
        "x",  a list of variables
        "a",  a list of nonzero numbers
        "c",  a nonzero number
        "group",  a list [[k1,c1],[k2,c2], ...] representing the isotrop group of d1, d2, ....

    OUTPUT::

         "[g, r_list]", a list with r_list = [[d_1, n_1, e_1], [d_2, n_2, e_2], ...], such that 

                    f = c * tau(g) - g + n_1/d_1^{e_1} + n_2/d_2^{e_2} + ...
                    
                where f = n_11/ tau^{k_11}(d_1)^{e_11} + n_12/ tau^{k_12}(d_1)^{e_12}...
                is the rational function corresponding to "L";
                g is a rational function, d_i is a polynomial, n is a polynomial in x1, e is an integer;
                tau(g(x)) = g(a*x) and a*x = [a_1*x_1, ..., a_n*x_n] 
                if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].

    OPTIONAL::
        
        If group != None, return "[g, r_list], Gp", where Gp = {d_1:[k_1, c_1], d2:[k_2, c_2], ...} such that
        tau^{k_1} (d_1) = c_1 * d_1, tau^{k_2} (d_2) = c_2 * d_2, ...

    Example::

        sage: R.<x1> =  PolynomialRing(QQ)
        sage: T.<x2> = R.fraction_field()['x2']
        sage: x1,x2 = R.gen(),T.gen()
        sage: S = T.fraction_field()   
        sage: S(x2+x2^2/expand((x2^2 + x1)*(4*x2^2 + 2*x1)*(x1+2)*(-x1+2)) + x2/(x2+x1)^2 + x2/(x2-x1))
        sage: x, a, c = [x1, x2], [2,2], 2
        sage: L, Gp = orbital_partial_fraction(f, x1, x, a, group = True)
        sage: L = L[1]
        sage: reduction(L, x, a, c, group = Gp)
        ([1/2/(1/4*x1^2*x2^2 + 1/4*x1^3 - 4*x2^2 - 4*x1),
          [[-x1 + x2, x1, 1],
           [x1 + x2, x2, 2],
           [x2^2 + x1, 3/8*x1^2/(1/4*x1^4 - 5*x1^2 + 16), 1]]],
         {-x1 + x2: [1, 2], x1 + x2: [1, 2], x2^2 + x1: [0, 1]})
    """
    g = 0
    r_list = []
    if group != None:
        Gp_dic = {}
        
    for d,orbit in L.items():
        g1, r1_list = reduce_one_orbit(d, orbit, x, a, c)
        g = g + g1
        if r1_list !=[]:
            r_list.append(r1_list)
            if group != None:
                Gp_dic[d] = group[d]
    
    if group == None:
        return [g, r_list]
    else:
        return [g, r_list], Gp_dic
        
        
def from_list_to_remainder(L):
    """
    convert a list representation to a rational function

    INPUT::

        "L", a list
        
            [[d_1, n_1, e_1], [d_2, n_2, e_2], ...]
                    
            representing a rational function
            
    OUTPUT::

        "f", a rational function such that f = n_1/d_1^{e_1} + n_2/d_2^{e_2}
    """
    f = 0
    for d, n, e in L:
        f = f + n/d**e
    return f

######################################################################################
## Part 4: decide the summability of multivariate rational functions
######################################################################################

def is_summable(f_, x_, a, c, *, info = False):
    """
    decide whether a given rational function f is summable or not, i.e., whether there exists another 
    rational function g such that 
                    f = c*tau(g) - g 
    where tau(g(x_1, ..., x_n)) = g(a_1*x_1, ..., a_n*x_n) if a = [a_1, ..., a_n] and x = [x_1, ..., x_n].
    
    INPUT:: 
    
        "f", a multivariate rational function over a subfield of QQbar
        "x", a list of variables
        "a", a list of nonzero numbers 
        "c", a nonzero number
        
    OUTPUT::
        "True, g",  if f = c*tau(g) - g for some ratonal function g, i.e. f is c*tau-summable
        "False",  if f is not c*tau-summable
    
    OPTIONAL::
        If "info = True", print some details about summability of a given rational function.
    """
    #### f should be viewed as a rational function in x_1, ..., x_{n} and x_{n} is the main variable
    f, x = make_main_variable(f_, x_, var_name = True)
    n = len(a)
    x_n = x[-1]
    a_n = a[-1]

    #### compute the orbital partial fraction decomposition of f w.r.t. x_n
    L, Gp = orbital_partial_fraction(f, x_n, x, a, group = True)
    p = L[0]

    #### reduce the proper fraction part of f
    [g, r_list], Gp =reduction(L[1], x, a, c, group = Gp)
    
    if p == 0 and r_list == []:
        return True, g
     
    #### decide whether the polynomial p in x_n is c*tau-summable or not
    if p != 0:

        ## get all nonzero coefficients of p w.r.t. x_n
        # p should be viewed as a polynomial in x_n
        p, xx  = make_main_variable(p, x, var_name = True, polynomial_ring = True)
        p_coeffs =[[i,p_i] for i, p_i in enumerate(p.list()) if p_i!=0]
    
        ## for each i, decide whether p_i is c * a_n^i * tau-summable or not by induction 
        for i, p_i in p_coeffs:
            if n == 1:
                if c*a_n^i - 1 != 0:
                    q_i = p_i/(c*a_n^i-1)
                else:
                    if info:
                        print("case 1: ", p_i*x_n^i, "is not ", c,"*tau-summable, where tau is represented by a =", a)
                    return False
            else: # n > 1
                pair = is_summable(p_i, xx[:-1], a[:-1], c*a_n^i,info=info)
                if pair == False:
                    return False
                else:
                    q_i = pair[1]
            ## Note: it seems that we can change the parent of g from QQ(x1,x2,x3) to QQ(x1,x2)(x3).
            ## But there is an error from QQ(x1)(x2)(x3) to QQ(x1,x2,x3).
            g = make_in_multi_fraction_field(g + q_i * x_n^i, x)

    #### decide whether the proper fraction represented by r_list is summable or not
    for d, num, e in r_list:
        
        ## obtain the isotropy group Gd of d
        k,mu = Gp[d] # tau^k(d) = mu * d
        
        if k == 0:
            ### if Gd is a trivial group, then num/d^e is c*tau-summable iff num = 0
            if info:
                print("case 2: ", num/d^e, "is not ", c,"*tau-summable, where tau is represented by a =", a)
            return False
        else: # k > 0
            cc = c^k * mu^(-e) 
            ### if Gd = <tau^k> is nontrivial, then num/d^e is c*tau-summable iff n is cc * tau^k - summable
            
            ## get all nonzero coefficients of num w.r.t. x_n
            # num should be viewed as a polynomial in x_n
            num, xx  = make_main_variable(num, x, var_name = True, polynomial_ring = True)
            num_coeffs =[[i, num_i] for i, num_i in enumerate(num.list()) if num_i!=0]

            ## for each i, decide whether num_i is cc * a_n^{k*i} * tau^k-summable or not by induction
            for i, num_i in num_coeffs:
                if n == 1:
                    if cc * a_n^(k*i)-1 != 0:
                        b_i = num_i/(cc * a_n^(k*i)-1)
                    else:
                        return False
                else: # n > 1
                    aa = [u^k for u in a[:-1]]
                    pair = is_summable(num_i, xx[:-1], aa, cc*a_n^(k*i))
                    if pair == False:
                        return False
                    else:
                        b_i = pair[1]
                g = g + sum([c**j * tau(b_i * x_n^i / d^e, x, a, j) for j in range(k)])
                g = make_in_multi_fraction_field(g, x)
    return True, g


def additive_decomposition(f_, x_, a, c, *, info = False):
    """
    decompose a given rational function f into 
                    f = c*tau(g) - g  + r
    where g, r are rational functions such that and f is c*tau-summable if and only if r = 0
    Here tau(g(x_1, ..., x_n)) = g(a_1*x_1, ..., a_n*x_n) if a = [a_1, ..., a_n] and x = [x_1, ..., x_n], such
    
    INPUT:: 
    
        "f", a multivariate rational function over a subfield of QQbar
        "x", a list of variables
        "a", a list of nonzero numbers 
        "c", a nonzero number
        
    OUTPUT::
        "g, r", two rational functions such that f = c*tau(g) - g + r and f is c*tau-summable if and only if r = 0
    
    OPTIONAL::
        If "info = True", print some details about summability of a given rational function.
        
    """
    #### f should be viewed as a rational function in x_1, ..., x_{n} and x_{n} is the main variable
    f, x = make_main_variable(f_, x_, var_name = True)
    n = len(a)
    x_n = x[-1]
    a_n = a[-1]

    #### compute the orbital partial fraction decomposition of f w.r.t. x_n
    L, Gp = orbital_partial_fraction(f, x_n, x, a, group = True)
    p = L[0]

    #### reduce the proper fraction part of f
    [g, r_list], Gp =reduction(L[1], x, a, c, group = Gp)
    
    if p == 0 and r_list == []:
        return g, 0
    
    #flag = True
    r = 0
    #### decide whether the polynomial p in x_n is c*tau-summable or not
    if p != 0:

        ## get all nonzero coefficients of p w.r.t. x_n
        # p should be viewed as a polynomial in x_n
        p, xx  = make_main_variable(p, x, var_name = True, polynomial_ring = True)
        p_coeffs =[[i,p_i] for i, p_i in enumerate(p.list()) if p_i!=0]

        ## for each i, decide whether p_i is c * a_n^i * tau-summable or not by induction
        for i, p_i in p_coeffs:
            if n == 1:
                if c*a_n^i - 1 != 0:
                    q_i = p_i/(c*a_n^i-1)
                else:
                    if info:
                        print("case 1: ", p_i*x_n^i, "is not ", c,"*tau-summable, where tau is represented by a =", a)
                    #flag = False
                    q_i = 0
                    r = r + p_i * x_n^i
            else: # n > 1
                pair = additive_decomposition(p_i, xx[:-1], a[:-1], c*a_n^i, info=info)
                #if pair[1] != 0: flag = False
                q_i = pair[0]
                r = r + pair[1] * x_n^i
            g = make_in_multi_fraction_field(g + q_i * x_n^i, x)
    
    #### decide whether the proper fraction represented by r_list is summable or not
    for d, num, e in r_list:
        
        ## obtain the isotropy group Gd of d
        k,mu = Gp[d] # tau^k(d) = mu * d
        
        if k == 0:
            ### if Gd is a trivial group, then num/d^e is c*tau-summable iff num = 0
            if info:
                print("case 2: ", num/d^e, "is not ", c,"*tau-summable, where tau is represented by a =", a)
            #flag = False
            r = r + num/d^e
        else: # k > 0
            cc = c^k * mu^(-e) 
            ### if Gd = <tau^k> is nontrivial, then num/d^e is c*tau-summable iff n is cc * tau^k - summable
            
            ## get all nonzero coefficients of num w.r.t. x_n
            # num should be viewed as a polynomial in x_n
            num, xx  = make_main_variable(num, x, var_name = True, polynomial_ring = True)
            num_coeffs =[[i, num_i] for i, num_i in enumerate(num.list()) if num_i!=0]

            ## for each i, decide whether num_i is cc * a_n^{k*i} * tau^k-summable or not by induction
            for i, num_i in num_coeffs:
                if n == 1:
                    if cc * a_n^(k*i)-1 != 0:
                        b_i = num_i/(cc * a_n^(k*i)-1)
                    else:
                        #flag = False
                        b_i = 0
                        r = r + num_i * x_n^i / d^e
                        r = make_in_multi_fraction_field(r, x)
                else: # n > 1
                    aa = [u^k for u in a[:-1]]
                    pair = additive_decomposition(num_i, xx[:-1], aa, cc*a_n^(k*i))
                    # if pair[1] != 0: flag = False
                    b_i = pair[0]
                    r = r + pair[1] * x_n^i / d^e
                    r = make_in_multi_fraction_field(r, x)
                g = g + sum([c**j * tau(b_i * x_n^i / d^e, x, a, j) for j in range(k)])
                g = make_in_multi_fraction_field(g, x)
    return g, r

