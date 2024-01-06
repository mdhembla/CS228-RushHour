# Rush-Hour

This exercise is inspired by the eponymous sliding block game:
https://en.wikipedia.org/wiki/Rush_Hour_(puzzle)

Here is the description of the exercise:
1) There is an n x n grid
2) A set of 2 x 1 cars are positioned on the grid. They are oriented horizontally or vertically.
   - Each car can move forward or backward in the direction of the car if another car is not blocking the car.
   - A move is shifting any one car by a single block
3) A special red car, which moves horizontally.
   - The goal is to get the red car to the rightmost end of its lane within a given number of moves (referred to as "limit")
4) There are some 1 x 1 mines on the grid. A car cannot drive over a mine.
5) Cars cannot collide with each other

Example:
      0    1    2    3    4    5
0	|    |    |    | X  |    |    |
	|____|____|____|____|____|____|
1	|    |    |    | V1 |    |    |
	|____|____|____|____|____|____|
2	|    | R  | R  | V1 |    | V2 |
	|____|____|____|____|____|____|
3	|    | X  | H  | H  |    | V2 |
	|____|____|____|____|____|____|
4	|    |    |    |    |    |    |
	|____|____|____|____|____|____|
5  |    |    |    |    |    |    |
	|____|____|____|____|____|____|

In the above diagram, the red car is denoted with the letter R is located in
row two. There are two vertical cars (V1 and V2), and one other horizontal car (H).
There are two mines, each denoted by the letter X. The goal is to bring R to column 5.

### INPUT FORMAT

We will describe objects on the grid by 3 comma-separated non-negative integers:
- orientation: 0 for vertical car, 1 for horizontal car, 2 for mine
- location: row,column
    * for cars, if the location of a vertical car is given as (i, j), it stands on (i, j) and (i+1, j)
    * likewise, the location of a horizontal car occupying (i, j) and (i, j+1) is given by (i, j)
	
The Red Car moves horizontally, so we omit the orientation for it.

Thus, the input is as follows.

First line: the dimension of the grid "n", and the maximum number of moves "limit"
   -Example: "6,17" means "the red car needs to reach the right edge of the 6x6 grid in at most 17 moves"

Second line: location of the red car.

The remaining lines: descriptions of the rest of the objects, as explained above.

Here is the input for the above example:

6,11
2,1
0,1,3
0,2,5
1,3,2
2,0,3
2,3,1

### OUTPUT FORMAT

Encode the above game as a SAT problem and use a SAT solver to find the moves to bring the red car to the exit within the given limit. 

- If the goal is not possible, your code should only print "unsat" and exit
	
- If the goal is possible, your code should print a sequence of moves, one per line
   * A move is two comma-separated non-negative integers
   * The pair denotes a position on the grid (row, column).
   * The car that occupies the position. moves and will move in a way such 
     that it will continue to occupy the position.

Example output:

3,5
4,5
3,3
3,4
2,3
3,3
2,2
2,3
2,4

The above sequence of moves solves the example grid.

### HARNESS
To generate inputs for testing, use this file as follows:

$ python3 generator.py foo.txt

The above command will produce a random input in foo.txt

Finally, verify the output with:

$ python3 simulate.py foo.txt bar.txt
