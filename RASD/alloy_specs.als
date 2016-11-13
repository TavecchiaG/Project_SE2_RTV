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

sig Time{
    progressive: Int
}{
    progressive>0
}

one sig ActualTime{
    time : Time
}{
    time.progressive>0
}

sig LicensePlate{}

sig DrivingLicense{}

sig Password{}

sig Code{}

/**AREA**/
abstract sig Area{
    position: Position
}

fact sameAreaSamePosition{
	all a1, a2: Area | (a1.position = a2.position) implies (a1 = a2)
}

sig SafeArea extends Area{}

sig UnsafeArea extends Area{}

/**POWERGRID**/
sig PowerGrid{
           iD: one Int,
           safeArea: one SafeArea,
    chargingCars: set Car,
    capacity: Int
}{
    #chargingCars <= capacity
}

/**CAR**/
sig  Car{
    licensePlate: LicensePlate,
    charge: Int,
    position: Position,
    passengers: Int,
           inCharge : Bool,
           outOfService : Bool,
}{
    charge >= 0 and charge <=100
    passengers > 0 and passengers <= 4
}

/**RESERVATION**/
sig Reservation{
            reservedCar: Car,
            user: User,
            startingTime: Time,
            endingTime: Time,
    unlockingCode: Code
}{
    endingTime.progressive > startingTime.progressive
}

/**USER**/
sig User{
          password : Password,
           suspendedService: Bool,
      drivingLicense: DrivingLicense
}

/**RIDE**/
sig Ride{
     startingPosition: Position,
     endingPosition: Position,
     startingTime: Time,
     endingTime: Time,
     passengers: Int,
     moneySaving: Bool,
    reservation: Reservation,
    charging: lone Charging,
    discount: set Discount
}{
    endingTime.progressive > startingTime.progressive
    startingTime.progressive < reservation.endingTime.progressive
    charging.plugginTime.progressive>endingTime.progressive
    passengers<reservation.reservedCar.passengers and passengers>0
}

/**DISCOUNT**/
//positive value is for malus
//negative value is for bonuses as stated in the document
sig Discount{
    value : Int
}{
    value=30 or value=-10 or value=-20 or value=-30
}

/**CHARGING**/
sig Charging{
   plugginTime: Time,
   powerGrid: PowerGrid   
}

/**DRAFT FACT**/
fact samePosition{
    all p1, p2: Position | (p1.latitude = p2.latitude and p1.longitude = p2.longitude) iff (p1 = p2)
}

fact noLicensePlateWithoutCar{
    all l : LicensePlate | (one c:Car | c.licensePlate=l)
}

fact noPasswordWithoutUser{
    all p:Password | (one u:User | u.password=p)
}

fact noDrivingLicenseWithoutUser{
    all dl:DrivingLicense | (one u:User | u.drivingLicense=dl)
}

fact noCodeWithoutReservation{
	all code: Code | (one res:Reservation| res.unlockingCode=code)
}

/**AREA FACT**/
fact allSafeAreasinMap{
    no s: SafeArea | not (s in Company.map)
}

/**POWERGRID FACT**/
fact onePGChargingOneCar{
    all disjoint pg1, pg2: PowerGrid | (pg1.chargingCars & pg2.chargingCars)=none
}

/**CAR FACT**/
fact uniqueLicensePlate{
    no disjoint c1, c2: Car | c1.licensePlate = c2.licensePlate
}

fact allCarstoCompany{
    no c: Car | not (c in Company.cars)
}

fact noCharginifOutofservice{
    all c: Car | (c.outOfService=True) => (c.inCharge=False)
}

fact ifBatteryLessThan5CarIsOutOfService{ 
    all c: Car| (c.charge<5) implies (c.outOfService=True)
}

fact carInChargingiffPG{
    all car: Car | (car.inCharge=True) iff (one pg:PowerGrid | car in pg.chargingCars and
        pg.safeArea.position=car.position)
}

fact noChargeThanNoPG{
    all car: Car | (car.inCharge=False) implies (no pg:PowerGrid | car in pg.chargingCars)
}

/**RESERVATION FACT**/
fact noResWithSuspendedService{
    no res:Reservation| res.user.suspendedService=True
}

fact noReservationOnUnavailableCar{
    no r: Reservation | r.reservedCar.outOfService = True
}

fact uniqueReservationPerTimePerUser{
    all disjoint r1,r2 : Reservation, u : User | ((r1.user=u) and (r2.user=u)) implies 
		((r1.startingTime!=r2.startingTime) and 
		((r2.startingTime.progressive>r1.endingTime.progressive) or 
		(r1.startingTime.progressive>r2.endingTime.progressive)))
}

fact differentCodeforDifferentReservation{
    no disjoint r1, r2: Reservation | r1.unlockingCode= r2.unlockingCode
}

/**USER FACT**/
fact uniquePassword{
     no disjoint u1,u2: User | u1.password=u2.password
}

fact uniqueDrivingLicense{
    no disjoint u1, u2: User | u1.drivingLicense = u2.drivingLicense
}

/**RIDE FACT**/
fact noUsingCarifinCharge{
	no r: Ride | r.reservation.reservedCar.inCharge=True
}

fact noUsingCarifOutOfService{
    no r: Ride | r.reservation.reservedCar.outOfService=True
}

fact sequentialReservation{
    all res1,res2: Reservation |
    ((res1.reservedCar = res2.reservedCar) => 
	((res1=res2) or 
	(res1.endingTime.progressive <= res2.startingTime.progressive) or 
	(res1.startingTime.progressive >= res2.endingTime.progressive)))
}

fact minus30{
    all ride:Ride | 
	(one disc: Discount| disc.value=-30 and disc in ride.discount) iff 
		(no disc2: Discount | disc2 in ride.discount and 
		(disc2.value=-20 or disc2.value=30))
}

fact minus20{
    all ride:Ride | 
	(one disc: Discount| disc.value=-20 and disc in ride.discount) iff 
		(no disc2: Discount | disc2 in ride.discount and (disc2.value=-30))
}

fact minus10{
    all ride:Ride | (one disc: Discount| disc.value=-10 and disc in ride.discount) iff 
	(no disc2: Discount | disc2 in ride.discount and (disc2.value=-30))
}

fact plus30{
    all ride:Ride| (one disc: Discount| disc.value=30 and disc in ride.discount) iff 
	(no disc2: Discount | disc2 in ride.discount and (disc2.value=-20 or disc2.value=-30))
}

fact noSameDiscounts{
    all ride: Ride | 
		(no disjoint d1,d2:Discount | 
			(d1 in ride.discount and d2 in ride.discount and d1.value=d2.value))
}

/**DISCOUNT**/
fact noDiscountWithoutRide{
    all disc : Discount | (one ride : Ride | disc in ride.discount)
}

/**MISC FACT**/
fact RideReservationTime{
    all ride: Ride , res: Reservation | 
	(ride.reservation.reservedCar=res.reservedCar) implies 
		(ride.reservation=res or 
		(res.startingTime.progressive>ride.endingTime.progressive) or
		(res.endingTime.progressive<ride.startingTime.progressive)) 
}
 
fact noReservationWithMoreRides{
    all res: Reservation, r1,r2: Ride | (r1.reservation=res implies(( r2.reservation!=res) or (r1=r2)))
}

fact NoChargingWithoutRide{
    all c:Charging | (one ride: Ride| ride.charging=c)
}

fact ifRideIsJustFinishedCarPositionEqualEndingPosition{
    all r : Ride, c : Car | 
	((r.endingTime=ActualTime.time) and (r.reservation.reservedCar=c)) implies 
		(r.endingPosition=c.position)
}

/**ASSERTION**/
assert noUserWithMultipleReservationSimultaneously{
    no disjoint u: User, r1,r2 : Reservation |  r1.user=u and r1.user=r2.user and 
	r1.startingTime.progressive=r2.startingTime.progressive
}

assert numberOfPassengersAlwaysLegal{
    no r: Ride | r.passengers>r.reservation.reservedCar.passengers
}

assert noRideIfReservationExpire{
    no ride: Ride | ride.startingTime.progressive>ride.reservation.endingTime.progressive
}

assert deletionWithoutFeePayment{
    #Reservation>0 implies 
	(some res:Reservation | res.endingTime.progressive<res.startingTime.progressive+35)
}

assert oneDriverPerRide{
    no disjoint u1,u2: User, disjoint r1,r2:Ride | 
	(r1.reservation.user=u1 and r2.reservation.user=u2 and 
	r1.reservation.reservedCar=r2.reservation.reservedCar and
	r1.startingTime.progressive=r2.startingTime.progressive and 
	r1.endingTime.progressive=r2.endingTime.progressive)
}

assert moneySavingOptionAvaliable{
    #Ride>0 implies (some r:Ride | r.moneySaving=True)
}

/**EXECUTION**/

pred show(){}
run show for 5 but 8 Int
check moneySavingOptionAvaliable
check oneDriverPerRide
check deletionWithoutFeePayment
check noRideIfReservationExpire
check numberOfPassengersAlwaysLegal
check noUserWithMultipleReservationSimultaneously
