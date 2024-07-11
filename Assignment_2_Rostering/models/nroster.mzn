% nurse rostering project
% STAGE A data
enum NURSE; % set of nurses to roster
enum SHIFT = { MORN, DAY, EVEN, NIGH, OFF };
int: nday;     % number of days for roster
set of int: DAYS = 1..nday; 
array[NURSE,DAYS] of bool: rostered_off; % nurse is guaranteed an off shift
% STAGE B data
int: maxweek; % maximum working shifts in any 7 day period
int: maxnightfort; % maximum night shifts in any 14 day period
int: minfort; % minimum number of working shifts in any 14 day period
array[SHIFT,DAYS] of int: minshift; % minimum number of nurses rostered on each shift
% STAGE C data
array[NURSE] of int: shift_cost;  
% STAGE D data
enum WARD;  % set of wards to roster
WARD: dummy; % dummy ward
array[WARD,DAYS] of int: minward; % minimum number of nurses rostered to each ward
constraint forall(d in DAYS)(assert(minward[dummy,d] = 0, "Dummy ward has non zero minimum on day \(d)\n"));
int: maxward; % maximum number of wards any nurse can work in the roster period
% STAGE E data
enum SKILL;
SKILL: senior;                         % which skill is senior
array[NURSE] of set of SKILL: skill;   % skills that each nurse has
array[WARD] of set of SKILL: required; % particular skills for each ward
opt WARD: emergency; % emergency ward if its being rostered
enum SLICE = { PREDAWN, AM, PM, LATE };
% coverage MORNING = {PREDAWN, AM}, 
%          DAY = {AM,PM} 
%          EVENING = {PM, LATE}, 
%          NIGHT {LATE, PREDAWN of the next day} 

%%%% DECISIONS
array[NURSE,DAYS] of var SHIFT: sh; % shift for each nurse on each day
var 0..nday*sum(shift_cost): total_cost;
array[NURSE,DAYS] of var WARD: wd; % ward rostered for each nurse

% --- Stage A
% A1
include "globals.mzn";
constraint forall(n in NURSE, i in DAYS) (
								% ward = OFF if rostered_off is true
								 rostered_off[n, i] = true -> sh[n, i] = OFF
);

% A2:
constraint forall(n in NURSE) (
								% 10 states, 5 actions, start from state 1, end from 2 to 10
								regular([sh[n, i] | i in DAYS], 10, 5, transition, 1, 2..10) 

);
array[1..10, SHIFT] of 0..10: transition = 
% Action (headings) = next day, work in:  MORN, DAY, EVEN, NIGH, OFF 
% State (columns) = after choose action:  START, MORN, DAY1, DAY2, EVEN, NIGH1, NIGH2, NIGH3, OFF1, OFF2
[|2,3,5,6,9 % START ->  MORN, DAY1, EVEN, NIGH1, OFF1 (go everywhere)
|2,3,5,6,9  % MORN  ->  MORN, DAY1, EVEN, NIGH1, OFF1 (go everywhere)
|0,4,0,0,0  % DAY1  ->  DAY2 (must 2 day in a row <=> must pick action DAY)
|2,4,5,6,9  % DAY2  ->  MORN, DAY2, EVEN, NIGH1, OFF1 (go everywhere)
|0,3,5,6,9  % EVEN  ->  DAY1, EVEN, NIGH1, OFF1 (can not pick MORN)
|0,0,5,7,9	  % NIGH1 ->  EVEN, NIGH2, OFF1 (can not pick MORN and DAY)
|0,0,5,8,9  % NIGH2 ->  EVEN, NIGH3, OFF1 (can not pick MORN and DAY)
|0,0,5,0,9  % NIGH3 ->  EVEN, OFF1 (can not pick MORN, DAY; can not have >= 3 NIGH in a row)
|2,3,5,6,10 % OFF1  ->  MORN, DAY1, EVEN, NIGH1, OFF2 (go everywhere)
|2,3,5,6,0  % OFF1  ->  MORN, DAY1, EVEN, NIGH1 (cannot have > 2 OFF)
|];

% -- Stage B
% B1 
array[SHIFT, DAYS] of var 0..card(NURSE): cnt_shift; % Counting number of nurse rostered to a particular shift in a day
constraint forall(d in DAYS) (global_cardinality(sh[..,d], SHIFT, cnt_shift[..,d]));
constraint forall(d in DAYS, shift in SHIFT) (
								cnt_shift[shift, d] >= minshift[shift, d]
);

% B2
constraint forall(n in NURSE) (
% sliding sum (low, up, sequence, array): sum all '1' in a sequence of 0/1 array. The total must be in a range (low, up)
								sliding_sum(0, maxweek, 7, [sh[n,i] != OFF | i in DAYS]) /\    % in 7 continous days, nurse works <= maxweek days
								sliding_sum(minfort, 14, 14, [sh[n,i] != OFF | i in DAYS]) /\  % in 14 continous days, nurse works >= minfort days
								sliding_sum(0, maxnightfort, 14, [sh[n,i] = NIGH | i in DAYS]) % in 14 continous days, nurse works in NIGH <= maxnightfort
);

% -- Stage C

constraint total_cost = sum(n in NURSE) (
						(sum(day in DAYS) (sh[n, day] != OFF)) * shift_cost[n] % shift works * cost per shift
);
solve minimize total_cost;

%-- Stage D
% D0: no work <=> no ward
constraint forall(n in NURSE, d in DAYS) (
								sh[n, d] = OFF <-> wd[n, d] = dummy
);

% D1
array [WARD, DAYS] of var 0..card(NURSE): cnt_ward; % counting number of nurse for a ward and day
constraint forall(d in DAYS) (
								global_cardinality(wd[..,d], WARD, cnt_ward[..,d])
);
constraint forall(d in DAYS, w in WARD) (
								cnt_ward[w, d] >= minward[w, d]							
);

% D2
% nvalue(wd[n,..]) count number of different ward per nurse
constraint forall(n in NURSE) (
								nvalue(wd[n,..]) <= maxward
);

%-- Stage E
% E1
constraint forall(d in DAYS, w in WARD)(
							cnt_ward[w,d] > 0 -> 				% at least 1 nurse in that ward
									forall(s in required[w])(  
												exists(n in NURSE)(wd[n,d] = w /\ s in skill[n])	 % then all skills must be covered
									)									
);

% E2
constraint forall(d in DAYS)(
								% pair of SHIFT which cover each SLICE, e.g. either NIGH (yesterday) or MORN can cover PREDAWN (today)
								exists(n in NURSE)(senior in skill[n] /\ ((sh[n,d-1] = NIGH) \/ (sh[n,d] = MORN))) /\ % PREDAWN
								exists(n in NURSE)(senior in skill[n] /\ ((sh[n,d] = MORN) \/ (sh[n,d] = DAY))) /\    % AM
								exists(n in NURSE)(senior in skill[n] /\ ((sh[n,d] = DAY) \/ (sh[n,d] = EVEN))) /\    % PM
								exists(n in NURSE)(senior in skill[n] /\ ((sh[n,d] = EVEN) \/ (sh[n,d] = NIGH)))      % LATE
);

% E3
constraint occurs(emergency) -> (
								forall(d in DAYS) (
											cnt_ward[emergency, d] = 0 \/ (
														cnt_ward[emergency, d] >= 4 /\ ( % only except 0 or >= 4 emergencies per day (NO 1, 2, 3)
														exists(n in NURSE)(wd[n,d] = emergency /\ sh[n,d] = MORN) /\
														exists(n in NURSE)(wd[n,d] = emergency /\ sh[n,d] = DAY) /\
														exists(n in NURSE)(wd[n,d] = emergency /\ sh[n,d] = EVEN) /\
														exists(n in NURSE)(wd[n,d] = emergency /\ sh[n,d] = NIGH) 
														)	
 											)
								)
);
