# LOST BAGGAGE DISTRIBUTION PROBLEM
# From H. P. Williams, Model building in mathematical programming. John Wiley & Sons, 2013.
# Section 12.27

### REQUIRED DATA PARAMETERS ###
param NumberOfVans >= 0, integer;
set Stops;
/*
the Origin (Heathrow) needs to be indicated as it has different constraints
than other Stops
"in Stops" means that it must be part of the Stops set
*/
param Origin symbolic, in Stops;
param TimeLimit >= 0;
param Distance { from in Stops, to in Stops };


### OPTIONAL DATA PARAMETERS ###
/*
this defines the max number of vans to be used to find the optimal time for each van
this only needs to be defined once the model is solved for the first objective
*/
param NumberOfVans_AfterSolvedFirst >= 0, integer;

/*
N is the number of Stops
it is only used to declare M
M is used in the linking constraints
it can be specified along with the data to add an additional
  "a van can visit at most M stops" constraint
*/
param N := card(Stops);
param M >= 0, default N;


### CALCULATED SYMBOLIC DATA ###
set Vans := 1..NumberOfVans;
/*
Edges is the Cartesian (cross) product of Stops producing a fully connected graph
*/
set Edges := Stops cross Stops;

/*
compute subsets of Stops that can be used for subtour elimination
2 or 3 node cycles are always broken, as even if they are not a subtour
  they usually indicate an incorrect solution
4 or 5 node cycles are only broken if they do not include the Origin
a heuristic used on 3-5 node subsets is to limit the cycle length to a fraction
  of the TimeLimit, this way long cycles that the solver wouldn't try anyway
  are not forming unnecessary constraints
the fractions were found from the excel solution's subtour elimination constraints
this is a heuristic to reduce the solve time, but can cause solutions
  including subtours, with different data
*/
set StopsMinusOrigin := Stops diff { Origin };

set subtoursOfLength2 := setof {
  a in Stops, b in Stops
  :  a <> b
} (a,b);
set subtoursOfLength3 := setof {
  a in Stops, b in Stops, c in Stops
  :  a <> b
  && a <> c
  && b <> c
  && Distance[a,b] + Distance[b,c] + Distance[c,a] < TimeLimit * 0.5
} (a,b,c);
set subtoursOfLength4 := setof {
  a in StopsMinusOrigin, b in StopsMinusOrigin, c in StopsMinusOrigin, d in StopsMinusOrigin
  :  a <> b
  && a <> c
  && a <> d
  && b <> c
  && b <> d
  && c <> d
  && Distance[a,b] + Distance[b,c] + Distance[c,d] + Distance[d,a] < TimeLimit * 0.6
} (a,b,c,d);
set subtoursOfLength5 := setof {
  a in StopsMinusOrigin, b in StopsMinusOrigin, c in StopsMinusOrigin, d in StopsMinusOrigin, e in StopsMinusOrigin
  :  a <> b
  && a <> c
  && a <> d
  && a <> e
  && b <> c
  && b <> d
  && b <> e
  && c <> d
  && c <> e
  && d <> e
  && Distance[a,b] + Distance[b,c] + Distance[c,d] + Distance[d,e]  + Distance[e,a] < TimeLimit * 0.67
} (a,b,c,d,e);

/* display how big each subset is for debug purposes *//*
display card(subtoursOfLength2);
display card(subtoursOfLength3);
display card(subtoursOfLength4);
display card(subtoursOfLength5);*/


### DECISION VARIABLES ###
/* whether van_i is used at all */
var usingVan { van in Vans }, binary;
/* whether van_i visits stop_j at all */
var vanVisitsStop { van in Vans, stop in Stops }, binary;
/* whether van_i uses the edge between stop_j and stop_k */
var vanGoesFromTo { van in Vans, (from, to) in Edges }, binary;


### OBJECTIVES ###
/* first optimize this *//*
##minimize vansUsed: sum { van in Vans } usingVan[van];*/


/* then optimize this when the min number of vans is know from the previous solution */
minimize maxTime:
  sum { (from, to) in Edges } vanGoesFromTo[1, from, to] * Distance[from, to];
s.t. vansUsed: sum { van in Vans } usingVan[van] = NumberOfVans_AfterSolvedFirst;

/*
alternatively use the multi objective optimisation formulation that finds the
optimal solution but takes a lot of time
*//*
minimize multi:
  TimeLimit * sum { van in Vans } usingVan[van]
  +
  sum { (from, to) in Edges } vanGoesFromTo[1, from, to] * Distance[from, to];*/


### CONSTRAINTS ###
subject to
  /*
  every stop must be visited exactly once
  an exception to this rule is Origin, since vans start the journey from
    there, therfore Origin should be visited once by every _used_ van
  */
  visitEveryStop { stop in Stops: stop <> Origin }:
    sum { van in Vans } vanVisitsStop[van, stop] = 1;
  originForEveryVan { van in Vans }:
    vanVisitsStop[van, Origin] = usingVan[van];

  /* link vanVisitsStop[*] and usingVan[*] binary variables */
  /* if using van then it should visit some stops */
  linking1 { van in Vans }:
    sum { stop in Stops } vanVisitsStop[van, stop] >= usingVan[van];
  /* if the van visits some stops then it must be used */
  linking2 { van in Vans }:
    sum { stop in Stops } vanVisitsStop[van, stop] <= M * usingVan[van];

  /* every van must enter a visited node exactly once */
  inOnce { van in Vans, to in Stops }:
    sum { from in Stops } vanGoesFromTo[van, from, to] = vanVisitsStop[van, to];

  /* every van must exit a visited node exactly once */
  outOnce { van in Vans, from in Stops }:
    sum { to in Stops } vanGoesFromTo[van, from, to] = vanVisitsStop[van, from];

  /* every van must do the whole trip under TimeLimit minutes */
  timeLimit { van in Vans }:
    sum { (from, to) in Edges } vanGoesFromTo[van, from, to] * Distance[from, to] <= TimeLimit;

  /*
  the first van should take the longest route,
  the second van should be the second longest route, etc.
  this way if the time taken by the first van is optimized then all vans take
    the optimal route
  */
  order { van in Vans: van <> 1 }:
    sum { (from, to) in Edges } vanGoesFromTo[van, from, to] * Distance[from, to]
    <=
    sum { (from, to) in Edges } vanGoesFromTo[van - 1, from, to] * Distance[from, to];

  /* eliminate cycles of length x using the sets calculated earlier */
  eliminateSubtoursOfLength2 { van in Vans, (a,b) in subtoursOfLength2 }:
    vanGoesFromTo[van,a,b] + vanGoesFromTo[van,b,a] <= 1;
  eliminateSubtoursOfLength3 { van in Vans, (a,b,c) in subtoursOfLength3 }:
    vanGoesFromTo[van,a,b] + vanGoesFromTo[van,b,c] + vanGoesFromTo[van,c,a] <= 2;
  eliminateSubtoursOfLength4 { van in Vans, (a,b,c,d) in subtoursOfLength4 }:
    vanGoesFromTo[van,a,b] + vanGoesFromTo[van,b,c] + vanGoesFromTo[van,c,d] + vanGoesFromTo[van,d,a] <= 3;
  eliminateSubtoursOfLength5 { van in Vans, (a,b,c,d,e) in subtoursOfLength5 }:
    vanGoesFromTo[van,a,b] + vanGoesFromTo[van,b,c] + vanGoesFromTo[van,c,d] + vanGoesFromTo[van,d,e] + vanGoesFromTo[van,e,a] <= 4;

solve;
### END OF MODEL ###

### DEBUG ###

/* export the solution as csv for verification or display *//*
param pre symbolic := "solution";
param post symbolic := ".csv";
param names symbolic := "names" & post;

printf Origin > names;
printf { stop in Stops: stop <> Origin } "," & stop >> names;

for { van in Vans } {
  printf "" > (pre & van) & post;
  for { from in Stops } {
    printf "%d", vanGoesFromTo[van, from, Origin] >> (pre & van) & post;
    printf { to in Stops: to <> Origin } ",%d", vanGoesFromTo[van, from, to] >> (pre & van) & post;
    printf "\n" >> (pre & van) & post;
  }
}*/

/* display the solution *//*
display timeLimit;*/


### DATA PARAMETERS ###
data;

/* limit NumberOfVans to 2 or 3 if you want a solution in feasible time */
param NumberOfVans := 6;
param NumberOfVans_AfterSolvedFirst := 2;

set Stops := Heathrow Harrow Ealing Holborn Sutton Dartford Bromley Greenwich
             Barking Hammersmith Kingston Richmond Battersea Islington Woolwich;
param Origin := Heathrow;

param TimeLimit := 120;

param Distance :            Heathrow  Harrow  Ealing  Holborn  Sutton  Dartford  Bromley  Greenwich  Barking  Hammersmith  Kingston  Richmond  Battersea  Islington  Woolwich :=
               Heathrow          999      20      25       35      65        90       85         80       86           25        35        20         44         35        82
               Harrow              0     999      15       35      60        55       57         85       90           25        35        30         37         20        40
               Ealing              0      15     999       30      50        70       55         50       65           10        25        15         24         20        90
               Holborn             0      35      30      999      45        60       53         55       47           12        22        20         12         10        21
               Sutton              0      60      50       45     999        46       15         45       75           25        11        19         15         25        25
               Dartford            0      55      70       60      46       999       15         15       25           45        65        53         43         63        70
               Bromley             0      57      55       53      15        15      999         17       25           41        25        33         27         45        30
               Greenwich           0      85      50       55      45        15       17        999       25           40        34        32         20         30        10
               Barking             0      90      65       47      75        25       25         25      999           65        70        72         61         45        13
               Hammersmith         0      25      10       12      25        45       41         40       65          999        20         8          7         15        25
               Kingston            0      35      25       22      11        65       25         34       70           20       999         5         12         45        65
               Richmond            0      30      15       20      19        53       33         32       72            8         5       999         14         34        56
               Battersea           0      37      24       12      15        43       27         20       61            7        12        14        999         30        40
               Islington           0      20      20       10      25        63       45         30       45           15        45        34         30        999        27
               Woolwich            0      40      90       21      25        70       30         10       13           25        65        56         40         27       999;

end;
