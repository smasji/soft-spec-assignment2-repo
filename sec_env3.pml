/*
	Elevator template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one elevator and two floors.
*/

// LTL formulas to be verified
//ltl p1 { []<> (floor_request_made[1]==true) } /* this property does not hold, as a request for floor 1 can be indefinitely postponed. */

// ltl a1 { [](floor_request_made[1] -> <>(current_floor == 1))}
// ltl a2 { [](floor_request_made[2] -> <>(current_floor == 2))}
// ltl b1 { []<> (cabin_door_is_open==true) } /* this property should hold, but does not yet; at any moment during an execution, the opening of the cabin door will happen at some later point. */
// ltl b2 { []<> (cabin_door_is_open==false)}



// the number of floors
#define N	4

// the number of elevators
#define M   4

ltl e1 { ((floor_request_made[0] == true) -> <>(floor_request_made[0] == false)) }
ltl e2 { []((floor_request_made[1] == true) -> <>(floor_request_made[1] == false)) }
ltl e3 { []((floor_request_made[2] == true) -> <>(floor_request_made[2] == false)) }
ltl e4 { []((floor_request_made[3] == true) -> <>(floor_request_made[3] == false)) }
ltl f1 { <>(total == M) }
ltl h { <>(floor_request_made[N-1] == true) }


// define all ID's
#define cabind_id 		_pid
#define elevatore_id	_pid - M
#define mainc_id		_pid - 2*M
#define reqid 			_pid - 3*M -1

// used for storing the next elevator in the elevator selection algo
byte next;
int total;

// type for direction of elevator, but we use 'direction'
mtype { down, up, none };

// asynchronous channel to handle passenger requests
chan request = [N] of { byte };

// status of requests per floor
bool floor_request_made[N];

typedef elevators {
	byte elevator[M];
}

typedef elevators_bool {
	bool elevator_bool[M];
}

// status of floor doors per shaft
elevators_bool floor_door_is_open[N];

// status and synchronous channels for elevator cabin and engine
byte current_floor[M];
bool cabin_door_is_open[M];
chan update_cabin_door[M] = [0] of { bool };
chan cabin_door_updated[M] = [0] of { bool };
chan move[M] = [0] of { bool };
chan floor_reached[M] = [0] of { bool };

// synchronous channels for communication between request handler and main control
chan go[M] = [0] of { byte };
chan served[M] = [0] of { bool };

// cabin door process
active [M] proctype cabin_door() {
	do
	:: update_cabin_door[cabind_id]?true -> floor_door_is_open[current_floor[cabind_id]].elevator_bool[cabind_id] = true; cabin_door_is_open[cabind_id] = true; cabin_door_updated[cabind_id]!true;
	:: update_cabin_door[cabind_id]?false -> cabin_door_is_open[cabind_id] = false; floor_door_is_open[current_floor[cabind_id]].elevator_bool[cabind_id] = false; cabin_door_updated[cabind_id]!false;
	od;
}

// process combining the elevator engine and sensors
active [M] proctype elevator_engine() {
	do
	:: move[elevatore_id]?true ->
		do
		:: move[elevatore_id]?false -> break;
		:: floor_reached[elevatore_id]!true; // reaches next floor
		od;
	od;
}

// DUMMY main control process. Remodel it to control the doors and the engine!
active [M] proctype main_control() { // should keep track of current floor and the direction of the elevator (A2 descr.)
	byte dest;
	int direction; // up is 1, down is -1, stationairy is 0;
	current_floor[mainc_id] = 0; // design choice: elevator starts at floor 1
	do
	:: go[mainc_id]?dest -> // receives from req_handler to go to dest

		// make sure doors are closed
		update_cabin_door[mainc_id]!false;
		cabin_door_updated[mainc_id]?false; //   wait for doors to be closed?

		if
		:: current_floor[mainc_id] < dest -> direction = 1 // should move up
		:: current_floor[mainc_id] > dest -> direction = -1 // should move down
		:: else -> direction = 0; // should not move
		fi

        if
        :: direction == 0 -> skip; // do not move
        :: else -> 
            move[mainc_id]!true; // make elevator move

            do // loop until dest is reached
            :: floor_reached[mainc_id]?true -> // wait for elevator to reach next floor
                current_floor[mainc_id] = current_floor[mainc_id] + direction; // update current floor accordingly
                if
                :: current_floor[mainc_id] == dest -> move[mainc_id]!false; direction = 0; break; // if elevator is at dest, stop the loop
                :: else -> skip; // else keep moving
                fi
            od
        fi
	   //  open doors
	   update_cabin_door[mainc_id]!true;
	   cabin_door_updated[mainc_id]?true; //   wait for doors to be opened?

	   floor_request_made[dest] = false;
	   served[mainc_id]!true;
	   assert(current_floor[mainc_id] == dest)
	od;
}

// request handler process. Remodel this process to serve M elevators!
active proctype req_handler() {
	byte dest;
	next = 0;
	total = 0;
	do
	:: request?dest -> go[next]!dest; served[next]?true; total = next + 1; next = (next+1) % M;
	//   request?dest is asynchronous, such that it can hold messages and serves as a queue
	//   served?true makes it wait until the request is served before receiving new requests
	od;
}

// request button associated to a floor i to request an elevator
active [N] proctype req_button() { //   0 <= reqid < N, and is equal to a floor nr
	do
	:: !floor_request_made[reqid] -> //   if there is no request for floor [reqid] ->
	   atomic {
		request!reqid;
		floor_request_made[reqid] = true;
	   }
	od;
}
