//ES 2018-2019 1st Project - Group 5
open util/ordering[Time] 
open util/integer
open util/ordering[Date]

sig Time {}

sig Date {}

sig Client {

	// 6
	accounts: set Account
	
}  

sig Broker extends Client {}

sig Bank {
	
	//5
	accounts: set Account

} 

sig Account {
	
	//3 and 4
	bank: one Bank,
	client: one Client,
	balance: Int -> Time

} {

	this in bank.accounts
	this in client.accounts

}

sig Hotel {
	
	//10
	rooms: set Room

}

abstract sig RoomType {}
sig Single, Double extends RoomType {}

sig Room {
	
	//11 and 12
	hotel: one Hotel,
	type: one RoomType	

}

sig RoomReservation {

	room: one Room,
	client: one Client,
	arrival: one Date,
	departure: one Date

} {
	
	//Departure date is after arrival date
	//13
	lt[arrival, departure]

}

sig ActivityProvider {
	
	activities: set Activity

}

sig Activity {

	activityProvider: one ActivityProvider,
	maxPeople: Int

} {

	//15
	maxPeople > 0

}

sig ActivityOffer {

	activity: one Activity,
	beginDate: one Date,
	endDate: one Date,
	availability: Int -> Time

} {

	//End date is after Begin date
	//16
	lt[beginDate, endDate]

}

sig ActivityReservation {
	
	activityOffer: one ActivityOffer,
	client: one Client,
	numPeople: Int

}{

	//18
	numPeople > 0	

}

abstract sig State {}
sig InitialState, PayedState, ConfirmedState extends State {}

sig Adventure {
	
	client: one Client,
	numPeople: Int,
	broker: one Broker,
	roomReservations: set RoomReservation,
	activityReservation: one ActivityReservation,
	cost: Int,
	clientAccount: one Account,
	brokerAccount: one Account,
	//21
	state: one State

} {

	// A client cannot be a broker 
	(client.accounts & broker.accounts) = none

	//22
	numPeople > 0

	//23
	client = activityReservation.client
	all rr : roomReservations | (rr.client = client)

	//27
	clientAccount in client.accounts

	//28
	brokerAccount in broker.accounts
	
	//24
	all disj rr1, rr2 : roomReservations | rr1.room.hotel = rr2.room.hotel
	
	//25
	#(roomReservations) = numPeople

}

abstract sig PurchaseType {}
sig Leisure, Business extends PurchaseType {}

sig Invoice {

	client: one Client,
	type: one PurchaseType,
	amount: Int,
	tax: Int
	
} 

one sig AdventureBuilder {

	currentAccounts: Account -> Time,
	
	currentRoomReservations: RoomReservation -> Time,

	currentActivityOffers: ActivityOffer -> Time,
	activityOfferAvailability: ActivityOffer -> Int -> Time,

	currentActivityReservations: ActivityReservation -> Time,
	
	currentAdventures: Adventure -> Time,
	adventureState: Adventure -> State -> Time,
	adventurePurchaseType: Adventure -> PurchaseType -> Time,

	currentInvoices: Invoice -> Time,
	invoiceClient: Invoice -> Client -> Time,

}

fact Traces {

	init[first]
	all t : Time - last | let t' = t.next |
		some a : Account, rr : RoomReservation, ao : ActivityOffer,ar : ActivityReservation, 
		adv : Adventure, inv : Invoice, c : Client, i : Int |
			openAccount[t, t', a] or
			openAccount[t, t', a] or
			clientDeposit[t, t', a, i] or
			makeActivityOffer[t, t', ao] or
			createAdventure[t, t', adv] or
			payAdventure[t, t', adv, inv] or
			cancelAdventure[t, t', adv, inv] or
			confirmAdventure[t, t', adv] or
			makeAnnualTaxRead[t, t', a] or
			deposit[t, t', a, i] or
			reserveActivity[t, t', ar] or
			cancelActivityReservation[t, t', ar] or
			reserveRooms[t, t', rr] or
			cancelRoomReservations[t, t', rr] or
			makeInvoice[t, t', inv] or
			cancelInvoice[t, t', inv] or
			removeClientInvoices[t, t', inv, c]

}

pred init(t: Time) {

	no AdventureBuilder.currentAccounts.t

	no AdventureBuilder.currentRoomReservations.t

	no AdventureBuilder.currentActivityOffers.t
	no AdventureBuilder.activityOfferAvailability.t

	no AdventureBuilder.currentActivityReservations.t
	
	no AdventureBuilder.currentAdventures.t
	no AdventureBuilder.adventureState.t
	no AdventureBuilder.adventurePurchaseType.t

	no AdventureBuilder.currentInvoices.t
	no AdventureBuilder.invoiceClient.t

}	

// MAIN OPERATIONS

//1
pred openAccount(t, t' : Time, a : Account) {
	
	//pre-cond
	//2
	not a in AdventureBuilder.currentAccounts.t

	//Open accounts start with balance 0
	//post-cond
	a.balance.t' = 0

	//post-cond
	//9
	AdventureBuilder.currentAccounts.t' = AdventureBuilder.currentAccounts.t + a
	

	//frame-conds
	noAccountsChangeExcept[t, t', a]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}

pred clientDeposit(t, t' : Time, a : Account, amount : Int) {

	deposit[t, t', a, amount]

}

pred makeActivityOffer(t, t' : Time, ao : ActivityOffer) {

	//pre-cond
	not ao in AdventureBuilder.currentActivityOffers.t
	
	//pre-cond
	//16
	lt[ao.beginDate, ao.endDate]
	
	//pre-cond
	//17
	ao.availability.t >= 0
	ao.availability.t <= ao.activity.maxPeople
	
	//post-cond
	//20
	AdventureBuilder.currentActivityOffers.t' = AdventureBuilder.currentActivityOffers.t + ao
	
	//post-cond
	AdventureBuilder.activityOfferAvailability.t'[ao] = ao.availability.t

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', ao]
	noActivityOfferAvailabilityChangeExcept[t, t', ao]
	noActivityReservationsChangeExcept[t, t', activityOffer.ao]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}

pred createAdventure(t, t' : Time, a : Adventure) {
	
	//pre-cond
	not a in AdventureBuilder.currentAdventures.t
	
	//pre-conds
	//If the client account is in CurrentAccounts it means that if eventually this client pays the adventure, the client will have an invoice and at least an open Bank account
	//33
	a.clientAccount in AdventureBuilder.currentAccounts.t
	a.brokerAccount in AdventureBuilder.currentAccounts.t

	//pre-cond
	//22
	a.numPeople > 0
	
	//pre-conds
	//23
	a.client = a.activityReservation.client
	all rr : a.roomReservations | (rr.client = a.client)
	
	//pre-cond
	//24
	all disj rr1, rr2 : a.roomReservations | rr1.room.hotel = rr2.room.hotel
	
	//pre-cond
	//25
	#(a.roomReservations) = a.numPeople	

	//pre-cond
	//27
	(a.clientAccount & a.client.accounts) != none
	
	//pre-cond
	//28
	(a.brokerAccount & a.broker.accounts) != none
	
	//post-cond
	AdventureBuilder.adventureState.t'[a] = InitialState
	
	//post-cond
	AdventureBuilder.currentAdventures.t' = AdventureBuilder.currentAdventures.t + a
	

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', a.roomReservations]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', a.activityReservation]
	noAdventuresChangeExcept[t, t', a]
	noAdventureStateChangeExcept[t, t', a]
	noAdventurePurchaseTypeChangeExcept[t, t', a]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}

pred payAdventure(t, t' : Time,  a : Adventure, i : Invoice) {
	
	//pre-cond
	//26	
	a in AdventureBuilder.currentAdventures.t
	
	//pre-cond
	//31
	AdventureBuilder.adventureState.t[a] = InitialState
	
	//Makes both reservations (activity and rooms)
	reserveActivity[t, t', a.activityReservation]
	reserveRooms[t, t', a.roomReservations]
	
	//pre-cond
	//Assuming that each adventure is associated with only one type of PurchaseType
	//An adventure can only be for Leisure or Business
	not a in (AdventureBuilder.adventurePurchaseType.t).univ

	//post-cond
	AdventureBuilder.adventurePurchaseType.t'[a] = Leisure

	//pre-cond
	//37
	//Calculates the tax given the cost of the adventure and purchase type
	(calculateTax[t, t', a.cost, AdventureBuilder.adventurePurchaseType.t[a]]) > 0
	
	//Makes both deposits into the broker's and client's accounts
	deposit[t, t', a.clientAccount, minus[0, plus[a.cost, calculateTax[t, t', a.cost, AdventureBuilder.adventurePurchaseType.t[a]]]]]
	deposit[t, t', a.brokerAccount, a.cost]
	

	//post-cond
	AdventureBuilder.adventureState.t'[a] = PayedState 

	//35 and 36
	makeInvoice[t, t', i]

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', a.roomReservations]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', a.activityReservation]
	noAdventuresChangeExcept[t, t', a]
	noAdventureStateChangeExcept[t, t', a]
	noAdventurePurchaseTypeChangeExcept[t, t', a]
	noInvoicesChangeExcept[t, t', i]
	noInvoiceClientChangeExcept[t, t', i]

}

pred cancelAdventure(t, t' : Time, a : Adventure, i : Invoice) {

	//pre-cond
	a in AdventureBuilder.currentAdventures.t
	
	//pre-cond
	//29
	AdventureBuilder.adventureState.t[a] = PayedState
	
	//Cancels both reservations(activity and rooms)
	//30
	cancelActivityReservation[t, t', a.activityReservation]
	cancelRoomReservations[t, t', a.roomReservations]
	
	//Undos both deposits made
	deposit[t, t', a.clientAccount,  plus[a.cost, calculateTax[t, t', a.cost, AdventureBuilder.adventurePurchaseType.t[a]]]]
	deposit[t, t', a.brokerAccount, minus[0, a.cost]]
	
	//post-conds
	//Removes the adventure
	AdventureBuilder.currentAdventures.t' = AdventureBuilder.currentAdventures.t - a
	AdventureBuilder.adventureState.t' = AdventureBuilder.adventureState.t - (a <: AdventureBuilder.adventureState.t)
	AdventureBuilder.adventurePurchaseType.t' = AdventureBuilder.adventurePurchaseType.t - (a <: AdventureBuilder.adventurePurchaseType.t)
	
	//Removes the invoice
	cancelInvoice[t, t', i]

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', a.roomReservations]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', a.activityReservation]
	noAdventuresChangeExcept[t, t', a]
	noAdventureStateChangeExcept[t, t', a]
	noAdventurePurchaseTypeChangeExcept[t, t', a]
	noInvoicesChangeExcept[t, t', i]
	noInvoiceClientChangeExcept[t, t', i]	

}

pred confirmAdventure(t, t' : Time, a : Adventure) {

	//pre-cond
	a in AdventureBuilder.currentAdventures.t
	
	//pre-cond
	//32
	AdventureBuilder.adventureState.t[a] = PayedState

	//post-cond
	AdventureBuilder.adventureState.t'[a] = ConfirmedState 

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', a.roomReservations]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', a.activityReservation]
	noAdventuresChangeExcept[t, t', a]
	noAdventureStateChangeExcept[t, t', a]
	noAdventurePurchaseTypeChangeExcept[t, t', a]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}

pred makeAnnualTaxRead(t, t' : Time, accounts : set Account) {

	//pre-cond
	accounts in AdventureBuilder.currentAccounts.t	
	
	//pre-cond
	//39 and 40
	all a : accounts | calculateAnnualTaxReduction[t, t', (AdventureBuilder.invoiceClient.t :> a.client).univ] >= 0

	//post-cond
	//Deposits an account and removes the invoices of that client so if another account of that client is in the set the calculateAnnualTaxReduction will return 0 since there are no invoices of that client and therefore the client will
	//only be credited once
	//38 and 41
	all a : accounts | deposit[t, t', a, calculateAnnualTaxReduction[t, t', (AdventureBuilder.invoiceClient.t :> a.client).univ]] and removeClientInvoices[t, t', (AdventureBuilder.invoiceClient.t :> a.client).univ, a.client]

	//post-cond
	//34
	no AdventureBuilder.currentInvoices.t

	//frame-conds
	noAccountsChangeExcept[t, t', accounts]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}


// AUX OPERATIONS

pred deposit(t, t' : Time, a : Account, amount : Int) {
	
	//pre-cond
	//7
	a in AdventureBuilder.currentAccounts.t
	
	//8
	plus[a.balance.t, amount] >= 0

	//post-cond
	a.balance.t' = plus[a.balance.t, amount]


	//frame-conds
	noAccountsChangeExcept[t, t', a]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}

pred reserveActivity(t, t' : Time, ar : ActivityReservation) {

	//pre-cond
	not ar in AdventureBuilder.currentActivityReservations.t
	
	//pre-cond
	//18
	ar.numPeople > 0
	
	//pre-cond
	ar.activityOffer in AdventureBuilder.currentActivityOffers.t

	//pre-cond
	ar.numPeople <= AdventureBuilder.activityOfferAvailability.t[ar.activityOffer] 

	//post-cond
	//19
	AdventureBuilder.activityOfferAvailability.t'[ar.activityOffer] = minus [AdventureBuilder.activityOfferAvailability.t[ar.activityOffer], ar.numPeople]	
	
	//post-cond
	AdventureBuilder.currentActivityReservations.t' = AdventureBuilder.currentActivityReservations.t + ar

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', ar.activityOffer]
	noActivityOfferAvailabilityChangeExcept[t, t', ar.activityOffer]
	noActivityReservationsChangeExcept[t, t', ar]
	noAdventuresChangeExcept[t, t', activityReservation.ar]
	noAdventureStateChangeExcept[t, t', activityReservation.ar]
	noAdventurePurchaseTypeChangeExcept[t, t', activityReservation.ar]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]
	
}

pred cancelActivityReservation(t, t' : Time, ar : ActivityReservation) {

	//pre-cond
	ar in AdventureBuilder.currentActivityReservations.t
	
	//post-cond
	AdventureBuilder.activityOfferAvailability.t'[ar.activityOffer] = plus [AdventureBuilder.activityOfferAvailability.t[ar.activityOffer], ar.numPeople]

	//post-cond
	//30
	AdventureBuilder.currentActivityReservations.t' = AdventureBuilder.currentActivityReservations.t - ar

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', ar.activityOffer]
	noActivityOfferAvailabilityChangeExcept[t, t', ar.activityOffer]
	noActivityReservationsChangeExcept[t, t', ar]
	noAdventuresChangeExcept[t, t', activityReservation.ar]
	noAdventureStateChangeExcept[t, t', activityReservation.ar]
	noAdventurePurchaseTypeChangeExcept[t, t', activityReservation.ar]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]

}

pred reserveRooms(t, t' : Time, rr : set RoomReservation) {
	
	//pre-cond
	not rr in AdventureBuilder.currentRoomReservations.t
	
	//pre-cond
	//13
	all rr1 : rr | (lt[rr1.arrival, rr1.departure])
	
	//pre-cond
	//24
	all disj rr1, rr2 : rr | (rr1.arrival = rr2.arrival && rr1.departure = rr2.departure && rr1.room.hotel = rr2.room.hotel)
	
	//pre-cond
	//14
	all rr1 : AdventureBuilder.currentRoomReservations.t, rr2 : rr | (rr1.room = rr2.room) => ((lt[rr2.arrival, rr1.arrival]  && lt[rr2.departure, rr1.arrival]) || (gt[rr2.arrival, rr1.arrival] && gt[rr2.arrival, rr1.departure]))

	//post-cond
	AdventureBuilder.currentRoomReservations.t' = AdventureBuilder.currentRoomReservations.t + rr

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', rr]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', roomReservations.rr]
	noAdventureStateChangeExcept[t, t', roomReservations.rr]
	noAdventurePurchaseTypeChangeExcept[t, t', roomReservations.rr]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]
	
}

pred cancelRoomReservations(t, t' : Time, rr : set RoomReservation) {

	//pre-cond
	rr in AdventureBuilder.currentRoomReservations.t

	//post-cond
	AdventureBuilder.currentRoomReservations.t' = AdventureBuilder.currentRoomReservations.t - rr	

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', rr]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', roomReservations.rr]
	noAdventureStateChangeExcept[t, t', roomReservations.rr]
	noAdventurePurchaseTypeChangeExcept[t, t', roomReservations.rr]
	noInvoicesChangeExcept[t, t', none]
	noInvoiceClientChangeExcept[t, t', none]
}

pred makeInvoice(t, t' : Time, i : Invoice) {

	//pre-cond
	not i in AdventureBuilder.currentInvoices.t

	//post-conds
	AdventureBuilder.invoiceClient.t[i] = i.client
	AdventureBuilder.currentInvoices.t' = AdventureBuilder.currentInvoices.t + i

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', i]
	noInvoiceClientChangeExcept[t, t', i]	

}

pred cancelInvoice(t, t' : Time, i : Invoice) {

	//pre-cond
	i in AdventureBuilder.currentInvoices.t
	
	//post-cond
	AdventureBuilder.invoiceClient.t' = AdventureBuilder.invoiceClient.t - (i <: AdventureBuilder.invoiceClient.t)

	//post-cond
	//34
	AdventureBuilder.currentInvoices.t' = AdventureBuilder.currentInvoices.t - i

	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', i]
	noInvoiceClientChangeExcept[t, t', i]

}

pred removeClientInvoices(t, t' : Time, invoices : set Invoice, c : Client) {
	
	//pre-cond
	invoices in AdventureBuilder.currentInvoices.t

	//post-conds
	AdventureBuilder.invoiceClient.t' = AdventureBuilder.invoiceClient.t - (AdventureBuilder.invoiceClient.t :> c)	
	AdventureBuilder.currentInvoices.t' = AdventureBuilder.currentInvoices.t - invoices
	
	//frame-conds
	noAccountsChangeExcept[t, t', none]
	noRoomReservationsChangeExcept[t, t', none]
	noActivityOffersChangeExcept[t, t', none]
	noActivityOfferAvailabilityChangeExcept[t, t', none]
	noActivityReservationsChangeExcept[t, t', none]
	noAdventuresChangeExcept[t, t', none]
	noAdventureStateChangeExcept[t, t', none]
	noAdventurePurchaseTypeChangeExcept[t, t', none]
	noInvoicesChangeExcept[t, t', invoices]
	noInvoiceClientChangeExcept[t, t', invoices]
	
}

//Both functions to test the results
fun calculateTax(t, t' : Time, amount : Int, pt : PurchaseType) : one Int {

	23

}


fun calculateAnnualTaxReduction(t, t' : Time, i : set Invoice) : one Int {

	23

}

//noChange Operations

pred noAccountsChangeExcept(t, t' : Time, a : set Account) {

	AdventureBuilder.currentAccounts.t - a = AdventureBuilder.currentAccounts.t' - a
	
}

pred noRoomReservationsChangeExcept(t, t' : Time, rr : set RoomReservation) {

	AdventureBuilder.currentRoomReservations.t - rr = AdventureBuilder.currentRoomReservations.t' - rr

}

pred noActivityOffersChangeExcept(t, t' : Time, ao : set ActivityOffer) {

	AdventureBuilder.currentActivityOffers.t - ao = AdventureBuilder.currentActivityOffers.t' - ao

}

pred noActivityOfferAvailabilityChangeExcept(t, t' : Time, ao : set ActivityOffer) {

	all act : ActivityOffer - ao | AdventureBuilder.activityOfferAvailability.t[act] = AdventureBuilder.activityOfferAvailability.t'[act]

}

pred noActivityReservationsChangeExcept(t, t' : Time, ar : set ActivityReservation) {

	AdventureBuilder.currentActivityReservations.t - ar = AdventureBuilder.currentActivityReservations.t' - ar

}

pred noAdventuresChangeExcept(t, t' : Time, adv : set Adventure) {

	AdventureBuilder.currentAdventures.t - adv = AdventureBuilder.currentAdventures.t' - adv

}

pred noAdventureStateChangeExcept(t, t' : Time, a : set Adventure) {

	all adv : Adventure - a | AdventureBuilder.adventureState.t[adv] = AdventureBuilder.adventureState.t'[adv]

}

pred noAdventurePurchaseTypeChangeExcept(t, t' : Time, a : set Adventure) {

	all adv : Adventure - a | AdventureBuilder.adventurePurchaseType.t[adv] = AdventureBuilder.adventurePurchaseType.t'[adv]

}

pred noInvoicesChangeExcept(t, t' : Time, i : set Invoice) {

	AdventureBuilder.currentInvoices.t - i = AdventureBuilder.currentInvoices.t' - i

}

pred noInvoiceClientChangeExcept(t, t' : Time, i : set Invoice) {

	all inv : Invoice - i | AdventureBuilder.invoiceClient.t[inv] = AdventureBuilder.invoiceClient.t'[inv]

}

//Asserts

//1
assert everyAccountCanBeOpened {

	all t : Time, a : Account | 
		let t' = t.next | 
			openAccount[t, t', a] => a in AdventureBuilder.currentAccounts.t'

}

// 3 & 4
assert eachOpenAccountUniqueBelonging {
	
	all a : Account |
		#(a.client) = 1 && #(a.bank) =1

}

//8
assert noOpenAccountBalanceNegative  {
	
	all t : Time, i : Int, a : AdventureBuilder.currentAccounts.t | 
		let t' = t.next | 
			deposit[t, t', a, i] => a.balance.t' >= 0

}

//9 
assert openAccountsRemainOpen {
	
	all t, t' : Time, a : Account |
		openAccount[t, t', a] => a in AdventureBuilder.currentAccounts.t'		
	
}


// 14
assert noRoomReservationsOverlap {
	
	all t : Time, rr1 : RoomReservation, rr2 : AdventureBuilder.currentRoomReservations.t | let t' = t.next | (rr1.room = rr2.room) 
		and reserveRooms[t, t', rr1] =>  
			((lt[rr2.arrival, rr1.arrival]  && lt[rr2.departure, rr1.arrival]) ||
			(gt[rr2.arrival, rr1.arrival] && gt[rr2.arrival, rr1.departure]))

}


// 17
assert activityOfferAvailabilityValidValue {

	all t : Time, ao : ActivityOffer | let t' = t.next | makeActivityOffer[t, t', ao] =>
		ao.availability.t >= 0 && 
		(ao.availability.t <= ao.activity.maxPeople)

}

// 18
assert activityReservationIsForSomeone {

	all t : Time, a : ActivityReservation | 
		let t' = t.next | 
		reserveActivity[t, t', a] => a.numPeople > 0

}

//19
assert activityCapacityDecreases {

	all t : Time, ao : AdventureBuilder.currentActivityOffers.t,
			ar : ActivityReservation |
			let t' = t.next | (ar.activityOffer = ao) and
			reserveActivity[t, t', ar] => 
				AdventureBuilder.activityOfferAvailability.t[ao] > AdventureBuilder.activityOfferAvailability.t'[ao]

}

//22
assert adventureIsForSomeone {

	all t: Time, a : Adventure | 
		let t' = t.next | 
			createAdventure[t, t', a] => a.numPeople > 0

}

//29
assert onlyPayedAdventuresCanBeCancelled {

	all t : Time, i : Invoice, a : AdventureBuilder.currentAdventures.t | let t' = t.next |
		cancelAdventure[t, t', a, i] => AdventureBuilder.adventureState.t[a] = PayedState

}

//30
assert activityReservationsCanDisappearIfAdventuresIsCancelled {
	
	all t: Time, ar : AdventureBuilder.currentActivityReservations.t , a : AdventureBuilder.currentAdventures.t, i : AdventureBuilder.currentInvoices.t |
		let t' = t.next | (a.activityReservation = ar) and cancelAdventure[t, t', a, i] => not ar in AdventureBuilder.currentActivityReservations.t
			

}

//31
assert adventurePayedThenItWasCreated {

	all t : Time, i : Invoice, a : Adventure |
		let t' = t.next |
			payAdventure[t, t', a, i] => AdventureBuilder.adventureState.t[a] = InitialState

}

//32
assert adventureConfirmedThenItWasPayed {
	
	all t : Time, a : Adventure |
		let t' = t.next |
			confirmAdventure[t, t', a] => AdventureBuilder.adventureState.t[a] = PayedState

}

//33
assert clientWithInvoicesHaveAtLeastOneOpenBankAccount {

	all t : Time, inv : AdventureBuilder.currentInvoices.t |
		#(inv.client.accounts & AdventureBuilder.currentAccounts.t) > 0

}

//36
assert invoiceCreatedOnlyIfPayed {

	all t : Time, a : AdventureBuilder.currentAdventures.t, i : Invoice |
		let t' = t.next | makeInvoice[t, t', i] => AdventureBuilder.adventureState.t[a] = PayedState

}

//37
assert taxValid {

	all t : Time, i : AdventureBuilder.currentInvoices.t |
		i.tax >= 0

}

//39 & 40
assert balancesWontDecreaseButCanIncreaseWithTax {

	all t : Time, a : AdventureBuilder.currentAccounts.t |
		let t' = t.next |
			makeAnnualTaxRead[t,t',a] =>
				a.balance.t' >= a.balance.t

}

//41
assert clientWithoutInvoicesAreNotAffectedByAnnualTaxReduction {

	all t : Time, c : Client, i : AdventureBuilder.currentInvoices.t | let t' = t.next | 
		(c != i.client) and makeAnnualTaxRead[t, t', client.c]
			=> (client.c).balance.t = (client.c).balance.t' 

}

check everyAccountCanBeOpened
check eachOpenAccountUniqueBelonging
check openAccountsRemainOpen
check noOpenAccountBalanceNegative 
check noRoomReservationsOverlap
check activityOfferAvailabilityValidValue
check activityReservationIsForSomeone 
check activityCapacityDecreases
check adventureIsForSomeone
check activityReservationsCanDisappearIfAdventuresIsCancelled
check onlyPayedAdventuresCanBeCancelled
check adventurePayedThenItWasCreated
check adventureConfirmedThenItWasPayed 
check clientWithInvoicesHaveAtLeastOneOpenBankAccount
check invoiceCreatedOnlyIfPayed
check taxValid
check balancesWontDecreaseButCanIncreaseWithTax
check clientWithoutInvoicesAreNotAffectedByAnnualTaxReduction

run init for 1 but exactly 4 Time, 2 Date, 2 Account, 2 Client

