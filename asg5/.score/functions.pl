/* Assignment 5 */
/* Justin Clark judclark@ucsc.edu */
/* Guangyang Chen gchen34@ucsc.edu */

/* Prolog Not */
not( X ) :- X, !, fail.
not( _ ).

/* Degrees and Minutes to Radians */
dm_rad( degmin( Deg, Min ), Radians ) :-
   Radians is (Deg + Min / 60) * pi / 180.

/* Haversine method of finding great circle distance */
haversine_radians( Airport1, Airport2, Distance ) :-
   airport( Airport1, _, Lat1, Lng1 ),
   airport( Airport2, _, Lat2, Lng2 ),
   dm_rad( Lat1, RLat1 ),
   dm_rad( Lng1, RLng1 ),
   dm_rad( Lat2, RLat2 ),
   dm_rad( Lng2, RLng2 ),
   Dlat is RLat2 - RLat1,
   Dlng is RLng2 - RLng1,
   A is sin( Dlat / 2 ) ** 2
      + cos( RLat1 ) * cos( RLat2 ) * sin( Dlng / 2 ) ** 2,
   Dist is 2 * atan2( sqrt( A ), sqrt( 1 - A ) ),
   Distance is Dist * 3959.

/* Set time */
set_time( Hours, Minutes, ArriveHours, ArriveMinutes ) :- 
   Minutes < 60,
   ArriveHours is Hours,
   ArriveMinutes is Minutes.

/* Format time*/
format_time( Hours, Minutes, ArriveHours, ArriveMinutes ) :-
   Minutes >= 60,
   ArriveHours is Hours + 1,
   ArriveMinutes is Minutes - 60.  
  
/* Flight time */ 
flight_time( Airport1, Airport2, FlightTime ) :-
   haversine_radians( Airport1, Airport2, Distance),
   FlightTime is Distance / 500.  

/* Arrival time */
arrival_time( flight(Airport1, Airport2, time(DH,DM)), ArrivalTime) :-
   flight_time( Airport1, Airport2, FlightTime ),
   min_to_Hours( DH, DM, DepartureTime ),
   ArrivalTime is DepartureTime + FlightTime.

/* Mins to hours */
min_to_Hours( Hours, Minutes, HM ) :-
   HM is Hours + Minutes / 60.

hours_to_Minutes( Hours, Minutes ) :-
   Minutes is Hours * 60.
   
/* Format print time */
format_print( Digits ) :-
   Digits < 10, print( 0 ), print( Digits ).

format_print( Digits ) :-
   Digits >= 10, print( Digits ). 

/* Print time */
print_time( HoursMinutes ) :-
   RawMin is floor( HoursMinutes * 60 ),
   Hours is RawMin // 60,
   Minutes is RawMin mod 60,
   format_print( Hours ),
   print( ':' ),
   format_print( Minutes ).
   
/* Valid time */
valid_time( H1, time( H, M )) :-
   min_to_Hours( H, M, H2 ),
   H1 + (29//60) < H2.

/* Compile list of path from node to end */
listpath( Node, End, [flight( Node, Next, Dtime)|Outlist] ) :-
   not(Node = End),
   flight(Node, Next, Dtime),
   listpath( Next, End, [flight( Node, Next, Dtime)], Outlist ).
    
listpath( Node, Node, _, [] ).
listpath( Node, End,
   [flight( Dep, Arr, DepTime )| Tried],
   [flight( Node, Next, Dtime )| List] ) :-
   flight( Node, Next, Dtime),
   arrival_time( flight( Dep, Arr, DepTime ), TArrive),
   valid_time( TArrive, Dtime ),
   arrival_time( flight( Node, Next, Dtime ), ArrivalTime),
   ArrivalTime < 24,
   listpath( Next, End, [flight( Node, Next, Dtime )|Tried], List ). 

/* To upper case*/   
to_upper( Lower, Upper) :-
   atom_chars( Lower, Lowerlist),
   maplist( lower_upper, Lowerlist, Upperlist),
   atom_chars( Upper, Upperlist).

/* Write first applicable path */
writepath( [] ).   
writepath( [flight(Depart, Arrive, time(DH, DM))|List] ) :-
   airport( Depart, DLabel, _, _),
   airport( Arrive, ALabel, _, _),
   to_upper( Depart, DepartUpper),
   to_upper( Arrive, ArriveUpper),
   write('depart  '), write(DepartUpper), write('  '), write(DLabel),
   min_to_Hours( DH, DM, DepartTime ),
   print_time( DepartTime ), nl,
   write('arrive  '), write(ArriveUpper), write('  '), write(ALabel),   
   arrival_time( flight(Depart, Arrive, time(DH, DM)), ArrivalTime),
   print_time( ArrivalTime ), nl,
   writepath( List ).
   
/* Fly success */
fly( Depart, Arrive ) :-
   listpath( Depart, Arrive, List),
   nl,
   writepath(List), !.

/* Fly error time */
fly( Depart, Depart ) :-
   !, fail.

/* Fly error airport */
fly( _, _ ) :-
   !, fail.
