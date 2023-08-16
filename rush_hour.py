import re
from statistics import mode
import sys
from z3 import *
from time import time
start = time()

input_file = open(sys.argv[1],"r")
grid_initial_state = input_file.readlines()
for i in range(len(grid_initial_state)):
    grid_initial_state[i]=grid_initial_state[i].strip().split(',')
input_file.close()

grid_size = int(grid_initial_state[0][0])
limit = int(grid_initial_state[0][1])

red_car =  [ [ [ Bool("red_car_%s_%s_%s" % (i, j, k)) for k in range(limit+1)] for j in range(grid_size+2) ] for i in range(grid_size+2) ] 
vert_cars = [ [ [ Bool("vert_car_%s_%s_%s" % (i, j, k)) for k in range(limit+1)] for j in range(grid_size+2) ] for i in range(grid_size+2) ]
horz_cars = [ [ [ Bool("horz_car_%s_%s_%s" % (i, j, k)) for k in range(limit+1)] for j in range(grid_size+2) ] for i in range(grid_size+2) ]
mines = [ [Bool("mines_%s_%s" % (i,j)) for j in range(grid_size+2)] for i in range(grid_size+2) ]

rush_hour_solver=Solver()

dummy_list=[]
for i in range(grid_size+2):
    for j in range(grid_size+2):
        dummy_list.append((i,j))
x=int(grid_initial_state[1][0])
y=int(grid_initial_state[1][1])
rush_hour_solver.add(red_car[x+1][y+1][0]==True,vert_cars[x+1][y+1][0]==False,horz_cars[x+1][y+1][0]==False,mines[x+1][y+1]==False)
dummy_list.remove((x+1,y+1))
for i in range(2,len(grid_initial_state)):
    if grid_initial_state[i][0]=='0':
        x=int(grid_initial_state[i][1])
        y=int(grid_initial_state[i][2])
        dummy_list.remove((x+1,y+1))
        rush_hour_solver.add(vert_cars[x+1][y+1][0]==True,horz_cars[x+1][y+1][0]==False,mines[x+1][y+1]==False,red_car[x+1][y+1][0]==False)
    elif grid_initial_state[i][0]=='1':
        x=int(grid_initial_state[i][1])
        y=int(grid_initial_state[i][2])
        dummy_list.remove((x+1,y+1))
        rush_hour_solver.add(horz_cars[x+1][y+1][0]==True,vert_cars[x+1][y+1][0]==False,mines[x+1][y+1]==False,red_car[x+1][y+1][0]==False)
    else:
        x=int(grid_initial_state[i][1])
        y=int(grid_initial_state[i][2])
        dummy_list.remove((x+1,y+1))
        rush_hour_solver.add(mines[x+1][y+1]==True,horz_cars[x+1][y+1][0]==False,vert_cars[x+1][y+1][0]==False,red_car[x+1][y+1][0]==False)
for k in range(1, limit+1):
    for j in range(grid_size+2):
        for i in [0, grid_size+1]:
            rush_hour_solver.add(horz_cars[i][j][k]==False,vert_cars[i][j][k]==False,red_car[i][j][k]==False)
    for i in range(1, grid_size+1):
        for j in [0, grid_size+1]:
            rush_hour_solver.add(horz_cars[i][j][k]==False,vert_cars[i][j][k]==False,red_car[i][j][k]==False)

for i in range(len(dummy_list)):
    x=dummy_list[i][0]
    y=dummy_list[i][1]
    if x==0 or y==0 or x==grid_size+1 or y==grid_size+1:
        rush_hour_solver.add(vert_cars[x][y][0]==False,horz_cars[x][y][0]==False,mines[x][y]==True,red_car[x][y][0]==False)
    else:
        rush_hour_solver.add(vert_cars[x][y][0]==False,horz_cars[x][y][0]==False,mines[x][y]==False,red_car[x][y][0]==False)


def PossibilityFunction(red_cars,horz_cars,vert_cars,mines,k,solver,grid_size):
    for i in range(1,grid_size+1):
        for j in range(1,grid_size+1):
            formula_horizontal_new=Implies(horz_cars[i][j][k+1],
                And(Not(mines[i][j]),Not(mines[i][j+1]),
                    Or(horz_cars[i][j][k],
                    And(horz_cars[i][j-1][k],Not(red_cars[i][j+1][k]),Not(horz_cars[i][j+1][k]),Not(vert_cars[i][j+1][k]),Not(vert_cars[i-1][j+1][k])),
                    And(horz_cars[i][j+1][k],Not(red_cars[i][j-1][k]),Not(horz_cars[i][j-1][k]),Not(vert_cars[i-1][j][k]),Not(vert_cars[i][j][k])))
                    )
            )
            formula_vertical_new=Implies(vert_cars[i][j][k+1],
                And(
                    Not(mines[i][j]),Not(mines[i+1][j]),
                    Or(vert_cars[i][j][k],
                    And(vert_cars[i+1][j][k],Not(red_cars[i][j][k]),Not(red_cars[i][j-1][k]),Not(horz_cars[i][j][k]),Not(horz_cars[i][j-1][k]),Not(vert_cars[i-1][j][k])),
                    And(vert_cars[i-1][j][k],Not(red_cars[i+1][j][k]),Not(red_cars[i+1][j-1][k]),Not(horz_cars[i+1][j][k]),Not(horz_cars[i+1][j-1][k]),Not(vert_cars[i+1][j][k])))
                )
            )
            formula_red_new = Implies(red_cars[i][j][k+1],
                And(Not(mines[i][j]),Not(mines[i][j+1]),
                Or(red_cars[i][j][k],
                    And(red_cars[i][j-1][k],Not(red_cars[i][j+1][k]),Not(horz_cars[i][j+1][k]),Not(vert_cars[i][j+1][k]),Not(vert_cars[i-1][j+1][k])),
                    And(red_cars[i][j+1][k],Not(red_cars[i][j-1][k]),Not(horz_cars[i][j-1][k]),Not(vert_cars[i-1][j][k]),Not(vert_cars[i][j][k]))
                )
                )
            )
            formula_red_previous = Implies(red_cars[i][j][k],
            Or(And(red_cars[i][j][k+1],Not(red_cars[i][j+1][k+1]),Not(red_cars[i][j-1][k+1])),
            And(Not(red_cars[i][j][k+1]),red_cars[i][j+1][k+1],Not(red_cars[i][j-1][k+1])),
            And(Not(red_cars[i][j][k+1]),Not(red_cars[i][j+1][k+1]),red_cars[i][j-1][k+1])
            )
            )

            formula_horz_previous = Implies(horz_cars[i][j][k],
            Or(And(horz_cars[i][j][k+1],Not(horz_cars[i][j+1][k+1]),Not(horz_cars[i][j-1][k+1])),
            And(Not(horz_cars[i][j][k+1]),horz_cars[i][j+1][k+1],Not(horz_cars[i][j-1][k+1])),
            And(Not(horz_cars[i][j][k+1]),Not(horz_cars[i][j+1][k+1]),horz_cars[i][j-1][k+1])
            )
            )

            formula_vert_previous = Implies(vert_cars[i][j][k],
            Or(And(vert_cars[i][j][k+1],Not(vert_cars[i+1][j][k+1]),Not(vert_cars[i-1][j][k+1])),
            And(Not(vert_cars[i][j][k+1]),vert_cars[i+1][j][k+1],Not(vert_cars[i-1][j][k+1])),
            And(Not(vert_cars[i][j][k+1]),Not(vert_cars[i+1][j][k+1]),vert_cars[i-1][j][k+1])
            )
            )

            solver.add(formula_horizontal_new,formula_horz_previous,formula_red_new,formula_red_previous,formula_vertical_new,formula_vert_previous)
    Xor_list=[]
    for i in range(grid_size+2):
        for j in range(grid_size+2):
            Xor_list.append((Xor(vert_cars[i][j][k],vert_cars[i][j][k+1]),1))
            Xor_list.append((Xor(horz_cars[i][j][k],horz_cars[i][j][k+1]),1))
            Xor_list.append((Xor(red_cars[i][j][k],red_cars[i][j][k+1]),1))
    solver.add(PbLe(Xor_list,2))

for i in range(limit):
    PossibilityFunction(red_car,horz_cars,vert_cars,mines,i,rush_hour_solver,grid_size)

rush_hour_solver.add(red_car[int(grid_initial_state[1][0])+1][grid_size-1][limit]==True)

if str(rush_hour_solver.check())=="sat":
    model=rush_hour_solver.model()
    def python_xor(a,b):
        return a != b

    def print_change(model,state,grid_size):
        count=0
        for i in range(grid_size+2):
            for j in range(grid_size+2):
                if(python_xor(bool(model[vert_cars[i][j][state]]),bool(model[vert_cars[i][j][state+1]]))): 
                    if count==0:
                        count+=1
                    else:
                        print(i-1,j-1,sep=',')
                if(python_xor(bool(model[horz_cars[i][j][state]]),bool(model[horz_cars[i][j][state+1]]))):
                    if count==0:
                        count+=1
                    else:
                        print(i-1,j-1,sep=',')
                if(python_xor(bool(model[red_car[i][j][state]]),bool(model[red_car[i][j][state+1]]))):
                    if count==0:
                        count+=1
                    else:
                        print(i-1,j-1,sep=',')


    for i in range(limit):
        print_change(model,i,grid_size)
else:
    print("unsat")