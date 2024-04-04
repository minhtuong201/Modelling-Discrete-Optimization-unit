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
								 rostered_off[n, i] = true -> sh[n, i] = OFF
);
								
% A2
% constraint forall(nurse in NURSE) (
% 								forall(i in 1..nday-3) (
% 											(sh[nurse,i] = sh[nurse, i+1] 	/\ sh[nurse, i] = NIGH /\ sh[nurse,i] = sh[nurse, i+2]) -> 	sh[nurse, i+3] != NIGH
% 								)	
% );

% constraint forall(nurse in NURSE) (
% 								forall(i in 1..nday-1) (
% 											(sh[nurse, i] = NIGH -> sh[nurse, i+1] in {EVEN, NIGH, OFF})
% 									 /\ (sh[nurse, i] = EVEN -> sh[nurse, i+1] != MORN)
% 								)	
% );
					
% constraint forall(nurse in NURSE) (
% 								forall(i in 1..nday-2) (
% 										(sh[nurse, i] = OFF /\ sh[nurse, i+1] = OFF) ->  sh[nurse, i+2] != OFF
% 								)	
% );

% constraint forall(nurse in NURSE) (
% 								forall(i in 2..nday-1) 
% 								((sh[nurse, i] = DAY /\ sh[nurse, i-1] != DAY) -> sh[nurse, i + 1] = DAY) /\
% 								(sh[nurse, 1] = DAY -> sh[nurse, 2] = DAY)
% );

% Using regular constraint:
constraint forall(n in NURSE) (
								regular([sh[n, i] | i in DAYS], 10, 5, transition, 1, 2..10)

);
array[1..10, SHIFT] of 0..10: transition = 
% Action (headings) = MORN, DAY, EVEN, NIGH, OFF
% State (columns) = START, MORN, DAY1, DAY2, EVEN, NIGH1, NIGH2, NIGH3, OFF1, OFF2
[|2,3,5,6,9
|2,3,5,6,9
|0,4,0,0,0
|2,4,5,6,9
|0,3,5,6,9
|0,0,5,7,9
|0,0,5,8,9
|0,0,5,0,9
|2,3,5,6,10
|2,3,5,6,0
|];

% -- Stage B
% Max and Min work shifts constraint
constraint forall(n in NURSE) (
								forall(i in 1..nday-6) (sum(j in i..i+6)(sh[n, j] != OFF) <= maxweek ) /\
								forall(i in 1..nday-13) (sum(j in i..i+13)(sh[n, j] = NIGH) <= maxnightfort ) /\
								forall(i in 1..nday-13) (sum(j in i..i+13)(sh[n, j] != OFF) >= minfort )  
);

array[DAYS, SHIFT] of var 0..infinity: cnt_shift; % Counting number of nurse per shift and day
constraint forall(d in DAYS) (global_cardinality(sh[..,d], SHIFT, cnt_shift[d,..]));
constraint forall(d in DAYS) (
								forall(shift in SHIFT) (
											cnt_shift[d, shift] >= minshift[shift, d]
								)
							
);

% -- Stage C

constraint total_cost = sum(n in NURSE) (
						(sum(day in DAYS) (sh[n, day] != OFF)) * shift_cost[n]
);

solve minimize total_cost;

%-- Stage D
constraint forall(n in NURSE, d in DAYS) (
								sh[n, d] = OFF <-> wd[n, d] = dummy
);

array [WARD, DAYS] of var 0..infinity: cnt_ward; % counting number of nurse for each ward and day
constraint forall(d in DAYS) (
								global_cardinality(wd[..,d], WARD, cnt_ward[..,d])
);
constraint forall(d in DAYS) (
								forall(w in WARD) (
											cnt_ward[w, d] >= minward[w, d]
								)
);
constraint forall(n in NURSE) (
								card({wd[n,d] | d in DAYS}) <= maxward
);
								




















