open util/boolean
/**DRAFTS**/

one sig Company{
    cars: set Car,
    map: set SafeArea
}

sig Position{
    latitude: Int,     //should be float
    longitude: Int    //should be float
}

sig LicensePlate{}

sig DrivingLicense{}

sig Password{}

/**AREA**/

abstract sig Area{
    position: Position
}

sig SafeArea extends Area{}

fact allSafeAreasinMap{
    no s: SafeArea | not (s in Company.map)
}

sig UnsafeArea extends Area{}

/**POWERGRID**/

sig PowerGrid{
	safeArea: one SafeArea,
	chargingCars: set Car,
    capacity: Int
}{
    #chargingCars <= capacity
}

fact PowerGridinSafeArea{
	all p1, p2: PowerGrid, s1, s2: SafeArea |
	(((p1.safeArea = s1) and (p2.safeArea = s2)) => (p1=p2)) 
	and ((p1.safeArea=s1)=>((p1.safeArea!=s2) or (s1=s2)))
}

/**CAR**/

sig Car{
    licensePlate: LicensePlate,
    charge: Int,
    position: Position,
    passengers: Int,
    inCharge : Bool,
    outOfService : Bool
}{
	charge >= 0 and charge <=100
    passengers > 0 and passengers <= 4
}

fact uniqueLicensePlate{
    no disjoint c1, c2: Car | c1.licensePlate = c2.licensePlate
}

fact allCarstoCompany{
    no c: Car | not (c in Company.cars)
}

/**USER**/

sig User{
	password : Password,
	suspendedService: Bool,
	drivingLicense: DrivingLicense
}

fact uniquePassword{
     no disjoint u1,u2: User | u1.password!=u2.password
}

fact uniqueDrivingLicense{
    no disjoint u1, u2: User | u1.drivingLicense = u2.drivingLicense
}

sig Time{
             hour: Int,
             minute: Int,
             second: Int
}{
            hour>=0 and hour<24
            minute>=0 and minute<60
            second>=0 and second<60
}

/*
fun timeComparison (t1 : Time, t2 : Time) : Bool {
   {answer: Bool | 
         
   }
}
*/

sig Reservation{
	reservedCar: Car,
	user: User,
	startingTime: Time,
	duration: Time,
	data: Int // to semplify our life LOL :D
}

fact noOtherReservationTillReserved{}

/**RIDE**/

sig Ride{
	startingPosition: Position,
	endingPosition: Position,
	duration: Time,
	passengers: Int,
	moneySaving: Bool,
	reservation: Reservation,
	charging: lone Charging,
	discount: set Discount
}

//valori negativi = bonus
sig Discount{
	value : Int
}{
	value=30 or value=-10 or value=-20 or value=-30
}

sig Charging{
   plugginTime: Time,
   powerGrid: PowerGrid   
}

/**AREA FACT**/
fact sameAreaSamePosition{
    all a1, a2: Area | (a1.position = a2.position) implies (a1 = a2)
}

/**EXECUTION**/

pred show(){}
run show



