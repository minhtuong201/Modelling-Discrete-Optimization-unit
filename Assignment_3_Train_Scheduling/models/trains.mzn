% train scheduling
%%%%%%%%%%% Data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
enum STOP;                             % set of stops
STOP: dstop;                           % dummy stop
array[STOP] of int: minimal_wait;      % minimum wait time at station 
array[STOP,STOP] of opt 0..infinity: travel_time; % travel time from each stop to another <> if not possible
array[STOP] of int: platform;          % number of platforms at station
enum STYPE = { ORDINARY, HUB, TERMINUS };
array[STOP] of STYPE: stype;           % type of STOP
array[STOP] of int: skip_cost;         % cost to skip the station (per service)
enum LINE = { SING, DOUB, QUAD, NONE };
array[STOP,STOP] of LINE: line;        % line type between stops
                  
enum ROUTE;                            % a sequence of STOPs
int: max_route_length;                 % longest route in number of stops
set of int: STOPNO = 1..max_route_length;         
array[ROUTE] of STOPNO: rlength;       % length of route
array[ROUTE,STOPNO] of STOP: route;    % route definitions; 
   
enum SERVICE;                          % the set of services to be schedules                         
array[SERVICE] of ROUTE: sroute;       % the route for each service
int: makespan;                         % end of time considered;
set of int: TIME = 0..makespan;
TIME: min_sep;                         % min separation of services on the same line same direction
array[SERVICE] of TIME: service_start; % from when the service can start
array[SERVICE] of TIME: service_end;   % when the service ideally ends

enum ENGINE;                           % set of engines available
array[ENGINE] of STOP: start;          % start location for engines
enum SERVICEX = s(SERVICE) ++ e(ENGINE); 

%%%%%%%%%%% Decisions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

array[SERVICE,STOPNO] of var TIME: arrive;    % arrive time at each stop
array[SERVICE,STOPNO] of var TIME: depart;    % depart time at each stop
array[SERVICE,STOPNO] of var TIME: wait;      % wait time at each stop
array[SERVICE,STOPNO] of var bool: stopped;   % which stops are actually made                                                            
var 0..infinity: delay_obj;
var 0..infinity: skip_obj; 
array[SERVICE] of var ENGINE: engine;         % which engine is used for each service
array[SERVICE] of var SERVICEX: prev;         % previous service or engine

include "globals.mzn";
%---------Stage A---------
% No service starts (arrives) at its first station before it service start time
constraint forall(serv in SERVICE)(
									arrive[serv, 1] >= service_start[serv]
);

% The wait time at each stop is the depart time minus the arrive time
constraint forall(serv in SERVICE, stopno in STOPNO)(
									wait[serv, stopno] = depart[serv, stopno] - arrive[serv, stopno]
);

% The wait time at each stop is >= to the minimal wait time if stopped = true
constraint forall(serv in SERVICE, stopno in STOPNO where stopped[serv, stopno])(
									wait[serv, stopno] >= minimal_wait[route[sroute[serv], stopno]]
);

% The arrival time at the next stop >= expected travel time + departure timme from previous
constraint forall(serv in SERVICE, stopno in STOPNO1)(
												arrive[serv, stopno+1] =    
												 depart[serv, stopno] + 
												 travel_time[route[sroute[serv], stopno], route[sroute[serv], stopno+1]]
);

% dummy stop: force the depart of last dummy = depart of actual state 
% (all dummies's arrive depart, are forced between 2 equal value)
constraint forall(serv in SERVICE)(
									depart[serv, max_route_length] = depart[serv, rlength[sroute[serv]]]					
);

%---------Stage B---------
%  no more than platform[st] trains are ever waiting at stop st
constraint forall(stop in STOP where stop != dstop)(
								cumulative(
% 												if services use that stop, take the start = arrive and duration = wait
													[arrive[serv, stopno] | serv in SERVICE, stopno in STOPNO where stop = route[sroute[serv], stopno]],
													[wait[serv, stopno] | serv in SERVICE, stopno in STOPNO where stop = route[sroute[serv], stopno]],
% 												each use 1 platform, in total of platform[stop]
													[1 | serv in SERVICE, stopno in STOPNO where stop = route[sroute[serv], stopno]], 
													platform[stop]
								)
);

%---------Stage C---------
%  enforce all the HUB and TERMINUS stations are stopped at for each service.
constraint	 forall(serv in SERVICE, stopno in STOPNO 
									where stype[route[sroute[serv], stopno]] != ORDINARY)(
											stopped[serv, stopno] = true
);

% delay obj = difference of actual and plan ending time
constraint delay_obj = sum(serv in SERVICE)(abs(depart[serv, rlength[sroute[serv]]] - service_end[serv]));

% skip obj = sum all skip cost of non stop 
constraint skip_obj = sum(serv in SERVICE, stopno in STOPNO where stopped[serv, stopno] = false)(
													skip_cost[route[sroute[serv], stopno]]
);

solve minimize delay_obj + skip_obj;

%---------Stage D---------
% prev is different
constraint all_different(prev); 

constraint forall(s2 in SERVICE)(
% 								if prev is engine the start stop is same
									if prev[s2] in e(ENGINE) then (prev[s2] = e(engine[s2]) 
																						/\ start[engine[s2]] = route[sroute[s2],1])
% 								if prev is other service, engine is same, handover in the same stop and 
% 								depart of previous < arrive of next
									else
											exists(s1 in SERVICE where prev[s2] = s(s1)) (
																engine[s1] = engine[s2] /\  
																route[sroute[s1], rlength[sroute[s1]]] = route[sroute[s2], 1] /\
																depart[s1, rlength[sroute[s1]]]	<= arrive[s2, 1]  
											)
									endif
);

%---------Stage E---------
set of int: STOPNO1 = 1..max_route_length-1;

% whether a service goes through a specific ray track
predicate go_through(var SERVICE: serv, var STOPNO1: stopno, var STOP: st1, var STOP: st2) =
										route[sroute[serv], stopno] = st1 /\ route[sroute[serv], stopno+1] = st2; 

constraint forall(st1, st2 in STOP where line[st1, st2] = DOUB)(
							disjunctive(
% 										if they go through the stop, take their depart time as start and the duration is min sep 
											[if go_through(serv, stopno, st1, st2) then depart[serv, stopno] else 0 endif 
											| serv in SERVICE, stopno in STOPNO1],
											[if go_through(serv, stopno, st1, st2) then min_sep else 0 endif 
											| serv in SERVICE, stopno in STOPNO1]
							)		
);

% ---------Stage F---------
% Check whether 2 services go in opposite direction of any SING ray track
predicate opposite_direction(var SERVICE: s1, var SERVICE: s2, 
										var STOPNO1: n1, var STOPNO1: n2) =			
										line[route[sroute[s1], n1], route[sroute[s1], n1+1]] = SING /\ 
										route[sroute[s1], n1] = route[sroute[s2], n2+1] /\ 
										route[sroute[s1], n1+1] = route[sroute[s2], n2];

constraint forall(st1, st2 in STOP where line[st1, st2] = SING)(
							disjunctive(
% 										if they go through the stop, take their depart time as start and the duration is min sep 
											[if go_through(serv, stopno, st1, st2) then depart[serv, stopno] else 0 endif 
											| serv in SERVICE, stopno in STOPNO1],
											[if go_through(serv, stopno, st1, st2) then min_sep else 0 endif 
											| serv in SERVICE, stopno in STOPNO1]
							)		
);

constraint forall(s1, s2 in SERVICE, n1, n2 in STOPNO1 where s1 < s2)(
% 							if they are opposite, must wait other service finish using the raytrack
								opposite_direction(s1, s2, n1, n2) ->
										depart[s1, n1] >= arrive[s2, n2+1] \/ 
										depart[s2, n2] >= arrive[s1, n1+1]
); 

% ---------Stage G---------
% Minimal wait times are all non-negative.
constraint forall(stop in STOP)(
								assert(minimal_wait[stop] >= 0, "minimal_wait[\(stop)] < 0"));

% Skip cost is non-negative, skip cost for non-ordinary stations is zero.
constraint forall(stop in STOP)(
								assert(stype[stop] != ORDINARY -> skip_cost[stop] = 0, "stype[\(stop)] = \(stype[stop]) but skip_cost[\(stop)] != 0") /\
								assert(skip_cost[stop] >= 0, "skip_cost[\(stop)] < 0"));	
	
% Platform numbers are positive, except for the dummy stop.
% constraint forall(stop in STOP where stop != dstop)(
% 								assert(platform[stop] > 0, "platform[\(stop)] <= 0")
% );		

% Wait times, skip cost and platform numbers for the dummy stop are all 0.
constraint assert(minimal_wait[dstop] = 0, "minimal_wait[dummy_stop] != 0");
constraint assert(skip_cost[dstop] = 0, "skip_cost[dummy_stop] != 0");
constraint assert(platform[dstop] = 0, "platform[dummy_stop] != 0");

% Travel time to the dummy stop and from a stop to itself is 0.
constraint forall(stop in STOP)(
								assert(travel_time[stop, stop] = 0, 
												"travel_time[\(stop), \(stop)] != 0") /\ 
								assert(travel_time[stop, dstop] = 0 /\ travel_time[dstop, stop] = 0, 
												"travel_time between \(stop) and dummy_stop != 0"));


% Service end is no earlier than service start for each service.
constraint forall(serv in SERVICE)(
								assert(service_start[serv] <= service_end[serv], 
											"SERVICE \(serv): end time = \(service_end[serv]) < start time = \(service_start[serv])!"));

% The line type is symmetric, i.e. the line type from stop st1 to st2 is the same as the line type from stop st2 to st1.

constraint forall(st1, st2 in STOP)(
								assert(line[st1, st2] = line[st2,st1], 
											"line_type between (\(st1), \(st2)) are not symmetric!"));

% The line type agrees with the travel time, i.e. line type is NONE iff travel time is absent or travel time is 0.
constraint forall(st1, st2 in STOP)(
								assert(line[st1, st2] = NONE <-> 
								(travel_time[st1,st2] = <> \/ travel_time[st1,st2] = 0), 
									"line_type and travel_time of (\(st1), \(st2)) do NOT agree!\n line_type = \(line[st1, st2]) but travel_time = \(travel_time[st1,st2])"));

% The route lengths agree with the definitions in route, i.e. if a route is length smaller than the max route length, then the extra stops are filled with dummy stops, and dummy stops only appear at the end of a route.
constraint forall(r in ROUTE, stopno in STOPNO)(
								assert(route[r, stopno] = dstop <-> stopno > rlength[r], 
											 "\((r)) has route lengths = \(rlength[r]) but stop at position \(stopno) = \(route[r, stopno])"));

% Each two consecutive (non-dummy) stops occuring in a route are connected (not absent in travel time).
constraint forall(r in ROUTE, stopno in STOPNO1 where route[r, stopno] != dstop /\ route[r, stopno+1] != dstop)(
								assert(travel_time[route[r, stopno], route[r, stopno+1]] != <>, 
								"stop \(route[r, stopno]), \(route[r, stopno+1]) are consecutive in route \(r) but travel_time is absent!"));

