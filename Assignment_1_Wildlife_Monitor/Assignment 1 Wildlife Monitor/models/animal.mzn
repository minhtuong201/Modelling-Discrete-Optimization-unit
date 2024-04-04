enum LOC; % set of locations
LOC: base; % base location where information is collected
constraint assert(base = min(LOC),"base is not the first mentioned location\n");
int: n; % number of traps available
array[LOC] of int: wild; % amount of interesting wildlife at each location
array[LOC] of int: cost; % cost to setup trap at location, -ve means unavailable
constraint assert(cost[base] = 0, "Cost of base location is not 0\n");
array[LOC,LOC] of int: d; % distance from one location to another (symmetric)
constraint forall(l1, l2 in LOC where l1 <= l2)(assert(d[l1,l2] = d[l2,l1], "distance is not symmetric at \(l1) \(l2)\n"));
constraint forall(l in LOC)(assert(d[l,l] = 0, "self distance for \(l) is not zero\n"));
int: move; % movement distance of animals
int: link; % wireless link maximum communication distance;
int: mind; % mininum distance between two traps
int: opcost; % cost to maintain/operate camera trap
int: budget; % total budget for traps

set of int: PLACE0 = 0..n;
set of int: PLACE = 1..n;
array[PLACE0] of var LOC: x; % location where camera trap is placed (except 0)
array[PLACE] of var PLACE0: s; % location to send info (part C only)
var int: total_wild;

%%--------PART A---------%%
array[LOC] of var int: loco; % location covered
constraint x[0] = base;
constraint forall([d[x[i],x[j]] >= mind | i,j in PLACE where x[i] < x[j] /\ x[j] != base /\ x[i] != base]);
constraint forall([x[i] != x[j] | i,j in PLACE where i != j /\ x[i] != base]);
constraint forall([cost[x[i]] != -1 | i in PLACE]);
constraint forall(l in LOC) (
    loco[l] = sum([d[l, x[i]] <= move | i in PLACE where x[i] != base])
);
constraint total_wild = sum([wild[l] | l in LOC where loco[l] > 0]);
solve maximize total_wild;

%%--------PART B---------%%
constraint budget >= sum([cost[x[i]] | i in PLACE]) + sum([x[i] != base | i in PLACE]) * opcost;
constraint forall([x[i] = x[i + 1] <-> x[i] = base | i in 1..n-1]);

% %%--------PART C---------%%
constraint forall(i in PLACE)(d[x[i], x[s[i]]] <= link /\ i > s[i]);
constraint forall([s[i] = 0 | i in PLACE where x[i] = base]);






























% output("\(s)")