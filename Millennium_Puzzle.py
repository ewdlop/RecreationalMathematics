#import puzzle from Yu-Gi-Oh! 

import random

# Define the pieces of the puzzle
pieces = ["Piece 1", "Piece 2", "Piece 3", "Piece 4", "Piece 5", "Piece 6", "Piece 7"]

# Shuffle the pieces to simulate the puzzle being scrambled
random.shuffle(pieces)

def display_puzzle(puzzle):
    print("Current puzzle state:")
    for index, piece in enumerate(puzzle):
        print(f"{index + 1}. {piece}")

def solve_puzzle():
    print("Welcome to the Millennium Puzzle!")
    print("Your goal is to place the pieces in the correct order.")
    puzzle = pieces.copy()
    correct_order = sorted(pieces)  # The correct order of the pieces

    while puzzle != correct_order:
        display_puzzle(puzzle)
        print("Enter the number of the piece you want to move:")

        try:
            move_from = int(input("Move from position: ")) - 1
            move_to = int(input("Move to position: ")) - 1

            if 0 <= move_from < len(puzzle) and 0 <= move_to < len(puzzle):
                # Swap the pieces
                puzzle[move_from], puzzle[move_to] = puzzle[move_to], puzzle[move_from]
            else:
                print("Invalid positions. Try again.")
        except ValueError:
            print("Invalid input. Please enter a number.")
    
    print("Congratulations! You have solved the Millennium Puzzle!")
    display_puzzle(puzzle)

if __name__ == "__main__":
    solve_puzzle()
