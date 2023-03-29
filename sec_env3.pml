/*
	Elevator template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one elevator and two floors.
*/

// LTL formulas to be verified
//ltl p1 { []<> (floor_request_made[1]==true) } /* this property does not hold, as a request for floor 1 can be indefinitely postponed. */

ltl a1 { [](floor_request_made[1] -> <>(current_floor == 1))}
ltl a2 { [](floor_request_made[2] -> <>(current_floor == 2))}
ltl b1 { []<> (cabin_door_is_open==true) } /* this property should hold, but does not yet; at any moment during an execution, the opening of the cabin door will happen at some later point. */
ltl b2 { []<> (cabin_door_is_open==false)}

// the number of floors
#define N	4

// the number of elevators
#define M   4


// define all ID's
#define cabind_id 		_pid
#define elevatord_id	_pid - M
#define mainc_id		_pid - 2*M
#define reqid 			_pid - 3*M -1

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
	:: update_cabin_door?true -> floor_door_is_open[current_floor] = true; cabin_door_is_open = true; cabin_door_updated!true;
	:: update_cabin_door?false -> cabin_door_is_open = false; floor_door_is_open[current_floor] = false; cabin_door_updated!false;
	od;
}

// process combining the elevator engine and sensors
active [M] proctype elevator_engine() {
	do
	:: move?true ->
		do
		:: move?false -> break;
		:: floor_reached!true; // reaches next floor
		od;
	od;
}

// DUMMY main control process. Remodel it to control the doors and the engine!
active proctype [M] main_control() { // should keep track of current floor and the direction of the elevator (A2 descr.)
	byte dest;
	int direction; // up is 1, down is -1, stationairy is 0;
	current_floor = 0; // design choice: elevator starts at floor 1
	do
	:: go?dest -> // receives from req_handler to go to dest

	    assert(dest >= 0 && dest < N); // assert that dest is a valid floor

		// make sure doors are closed
		update_cabin_door!false;
		cabin_door_updated?false; //   wait for doors to be closed?
		assert(!(cabin_door_is_open))

		if
		:: current_floor < dest -> direction = 1 // should move up
		:: current_floor > dest -> direction = -1 // should move down
		:: else -> direction = 0; // should not move
		fi

        if
        :: direction == 0 -> skip; // do not move
        :: else -> 
            move!true;	// make elevator move

            do // loop until dest is reached
            :: floor_reached?true -> // wait for elevator to reach next floor
                current_floor = current_floor + direction; // update current floor accordingly
                if
                :: current_floor == dest -> move!false; direction = 0; break; // if elevator is at dest, stop the loop
                :: else -> skip; // else keep moving
                fi
            od
        fi
	   //  open doors
	   update_cabin_door!true;
	   cabin_door_updated?true; //   wait for doors to be opened?
	   assert(floor_door_is_open[current_floor])	   

	   // an example assertion.
	   assert(0 <= current_floor && current_floor < N);

	   floor_request_made[dest] = false;
	   served!true;
	od;
}

// request handler process. Remodel this process to serve M elevators!
active proctype req_handler() {
	byte dest;
	do
	:: request?dest -> go!dest; served?true;
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
