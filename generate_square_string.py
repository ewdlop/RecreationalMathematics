def generate_square_string(size):
    """
    Generates a square string of a given size.
    
    Parameters:
    size (int): The size of the square (number of rows and columns).

    Returns:
    str: The square string.
    """
    square_string = ""
    for i in range(size):
        row = ''.join(['#' for _ in range(size)])
        square_string += row + '\n'
    return square_string

# Example usage:
size = 5
square_string = generate_square_string(size)
print(square_string)
