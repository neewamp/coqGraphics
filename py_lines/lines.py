import math

# pythagorean theorem
def distance(p1, p2):
    dx = p2.x - p1.x
    dy = p2.y - p1.y
    return math.sqrt(dx**2 + dy**2)

# graphics library init
from graphics import *
win = GraphWin()

# start and end points
p1 = Point(1, 0)
p2 = Point(0, 20)

# displacement vector p2-p1
v = Point(p2.x - p1.x, p2.y - p1.y)
print(v)
# number of intermediate points to generate
num_points = int(distance(p1, p2))

# linear interpolation to generate the points
# for i = 1 to num_points-1
print (num_points)
for i in range(num_points)[1:]:
    p = Point(p1.x + v.x*(i/num_points), p1.y + v.y*(i/num_points))
    p.draw(win)

# draw the end points as well
p1.draw(win)
p2.draw(win)
input()
