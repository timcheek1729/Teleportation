needsPackage "NumericalAlgebraicGeometry"
needsPackage "MonodromySolver"

R = CC[t][x,y]
R1 = CC[x,y]
use R

inputSystem = {x^2+y^2-t,x^3-y^2+x}
root = point {{0.544,0.839_CC}}
seed = 1
epsilon = 0.2
orderDeg = 5

numVar = #inputSystem

ParamSystem = new MutableList
generatedParam = new MutableList
generatedRoots = new MutableList
use R1;

-- create the set of new parameters and substitute them into the system
for i from 0 to orderDeg-1 do {
    newParam = seed + epsilon*exp(2*pi*ii*i/orderDeg);
    generatedParam = append(generatedParam,newParam);
    ParamSystem = append(ParamSystem, polySystem(specializeSystem(point {{newParam}}, polySystem(inputSystem))));
 }

-- use newton to find the root of the family of the parametrized system
for i from 0 to orderDeg-1 do {
    generatedRoots = append(generatedRoots,newton(ParamSystem#i,root))
    }

-- add the solution pair for the seed (seed, root)
generatedParam = prepend(seed,generatedParam)
generatedRoots = prepend(root,generatedRoots)

peek generatedParam
peek generatedRoots

-- create a basis polynomials for lagrange interpolation
lagBasis = new MutableList

for i from 0 to orderDeg do {
    comp = 1;
    for j from 0 to orderDeg do {
        if i != j then {
            comp = comp * (t-generatedParam#j)/(generatedParam#i-generatedParam#j);
            }
        };
    lagBasis = append(lagBasis,comp)
    }

-- convert the basis into matrix form
lagBasis = matrix(vector toList lagBasis)

-- create a matrix to store the coeffients, i.e. the roots
L = for i from 0 to numVar-1 list for i from 0 to orderDeg list 1+ii
M = mutableMatrix L

for i from 0 to numVar-1 do {
    for j from 0 to orderDeg do {
        M_(i,j) = (coordinates (generatedRoots#j))_i
        }
    }

-- convert the mutable matrix of coefficient into matrix
M = matrix M

-- outputs the polySystem of interpolated polynomials, i.e. x_i(p).
intSys = polySystem(flatten(entries(M*lagBasis)))

peek intSys


-- Rational Function Approximation
degNum = 2

createApprox = (param, root) -> {
    param = toList param;
    root = toList root;
    L1 = for i from 0 to length param - 1 list for i from 0 to degNum + 1 list 1+ii;
    A = mutableMatrix L1;
    b = new MutableList;
    matrixFamily = new MutableList;
    vectorFamily = new MutableList;
    approxFamily = new MutableList;
    numFamily = new MutableList;
    denomFamily = new MutableList;
    
    for k from 0 to numVar - 1 do {
        b = {};
        for i from 0 to length param - 1 do {
            for j from 0 to degNum do {
                A_(i,j) = (param_i)^j
                };
            A_(i, degNum + 1) = -(param_i)*(coordinates (root#i))_k;
            b = append(b,(coordinates (root#i))_k);
            };
        approxFamily = append(approxFamily, solve(transpose(matrix(A))*matrix(A),transpose(matrix(A))*vector(b)))
        --matrixFamily = append(matrixFamily, matrix(A));
        --vectorFamily = append(vectorFamily, vector(toList b));
        };
    coeffs = toList approxFamily;
    
    for i from 0 to numVar - 1 do {
        R = 0;
        for j from 0 to degNum do {
            R = R + (coeffs_i)_j*t^j
            };
        print R;
        numFamily = append(numFamily,R);
        denomFamily = append(denomFamily, 1 + (coeffs_i)_(degNum + 1)*t);
        };
    return {toList numFamily, toList denomFamily}
}

createApprox(toList generatedParam, generatedRoots)
createApprox({1,2,3,4,5},{point {{1,1}},point {{4,6}}, point {{0,2}}, point {{3,7}}, point {{8,6}}})

evaluateAt = (p, g) -> {
    output = new MutableList;
    for i from 0 to numVar - 1 do {
        num = sub((g_0)_i, {t=>p});
        denom = sub((g_1)_i, {t=>p});
        output = append(output, num/denom)
        };
    
    return toList output;
    }

evaluateAt(2, createApprox(generatedParam, generatedRoots))
evaluateAt(2, createApprox({1,2,3,4,5},{point {{1,1}},point {{4,6}}, point {{0,2}}, point {{3,7}}, point {{8,6}}}))
