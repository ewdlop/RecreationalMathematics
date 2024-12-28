import sympy as sp

# Define the symbols for coordinates
t, x, y, z = sp.symbols('t x y z')
coords = [t, x, y, z]

# Define the metric tensor (example: Minkowski metric for simplicity)
g = sp.Matrix([[1, 0, 0, 0],
               [0, -1, 0, 0],
               [0, 0, -1, 0],
               [0, 0, 0, -1]])

# Calculate the inverse metric tensor
g_inv = g.inv()

# Define the Christoffel symbols
def christoffel_symbols(g, coords):
    n = len(coords)
    Gamma = sp.MutableDenseNDimArray.zeros(n, n, n)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                Gamma[i, j, k] = sp.Rational(1, 2) * sum(
                    g_inv[i, m] * (sp.diff(g[m, j], coords[k]) + sp.diff(g[m, k], coords[j]) - sp.diff(g[j, k], coords[m]))
                    for m in range(n)
                )
    return Gamma

Gamma = christoffel_symbols(g, coords)

# Calculate the Riemann curvature tensor
def riemann_tensor(Gamma, coords):
    n = len(coords)
    R = sp.MutableDenseNDimArray.zeros(n, n, n, n)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    R[i, j, k, l] = sp.diff(Gamma[i, j, l], coords[k]) - sp.diff(Gamma[i, j, k], coords[l])
                    R[i, j, k, l] += sum(Gamma[i, k, m] * Gamma[m, j, l] - Gamma[i, l, m] * Gamma[m, j, k] for m in range(n))
    return R

R = riemann_tensor(Gamma, coords)

# Calculate the Ricci tensor
def ricci_tensor(R):
    n = R.shape[0]
    Ricci = sp.MutableDenseNDimArray.zeros(n, n)
    for i in range(n):
        for j in range(n):
            Ricci[i, j] = sum(R[m, i, m, j] for m in range(n))
    return Ricci

Ricci = ricci_tensor(R)

# Calculate the Ricci scalar
def ricci_scalar(Ricci, g_inv):
    return sum(g_inv[i, j] * Ricci[i, j] for i in range(len(g_inv)) for j in range(len(g_inv)))

R_scalar = ricci_scalar(Ricci, g_inv)

# Calculate the Einstein tensor
def einstein_tensor(Ricci, R_scalar, g):
    G = Ricci - sp.Rational(1, 2) * g * R_scalar
    return G

G = einstein_tensor(Ricci, R_scalar, g)

# Define the stress-energy tensor (example: perfect fluid)
rho, p = sp.symbols('rho p')  # energy density and pressure
T = sp.Matrix([[rho, 0, 0, 0],
               [0, p, 0, 0],
               [0, 0, p, 0],
               [0, 0, 0, p]])

# Constants
G_const = sp.symbols('G')  # Gravitational constant
c = sp.symbols('c')  # Speed of light
kappa = 8 * sp.pi * G_const / c**4

# Define the cosmological constant
Lambda = sp.symbols('Lambda')

# Einstein field equations
EFE = G + Lambda * g - kappa * T

# Print the Einstein field equations
sp.pprint(EFE)
