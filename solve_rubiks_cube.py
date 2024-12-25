!pip install kociemba

import kociemba

def solve_rubiks_cube(cube_string):
    """
    Solves a Rubik's Cube using the Kociemba's algorithm.

    Parameters:
    cube_string (str): A 54-character string representing the state of the Rubik's Cube.
                       The string should follow the standard color notation (URFDLB).

    Returns:
    str: The solution string with the moves to solve the Rubik's Cube.
    """
    try:
        solution = kociemba.solve(cube_string)
        return solution
    except Exception as e:
        return str(e)

# Example usage:
# The cube_string should be a 54(3*3*6)-character string representing the state of the Rubik's Cube.
# Here's an example of a scrambled cube:
cube_string = "UUUUUUUUURRRRRRRRRFFFFFFFFFDDDDDDDDDLLLLLLLLLBBBBBBBBB"

# 24(2*2*6)
two_by_two_cube_string = "UUUUUUUURRRRRRRRFFFFFFFFDDDDDDDDLLLLLLLLBBBBBBBB"

solution = solve_rubiks_cube(cube_string)
print("Solution:", solution)

solution = solve_rubiks_cube(two_by_two_cube_string)
print("Solution:", solution)
