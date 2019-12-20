module metamodel[Time]
open util/ordering[Time] as TO

/**
 * A link corresponds to a physical connection medium.
 * A link connects a set of nodes at any one time.
 */
sig Link {
	connects: set Node -> Time
}

/**
 * A node corresponds to a physical device, capable of hosting a set components.
 */
sig Node {
	hosts: set Component -> Time
}

/**
 * An interface represents a coherent set of operations that can be realized by
 * a number of components.
 */
sig Interface {
	methods: set Method
}{
	all t:Time | one p:Port | this in p.requires.t
	all t:Time | one p:Port | this in p.provides.t
}

/**
 * The reification of an operation.
 */
sig Method {
}

/**
 * Components, as run-time instances, represent self-contained units of deployment.
 * A component belongs to exactly one domain, and is deployed on exactly one (not 
 * necessarily the same) node at all times (as it is a run-time instance).
 */
sig Component {
	uses: set Port -> Time
}{
	all t:Time | one n:Node | this in n.hosts.t
}

/**
 * 
 */
sig Port {
	requires: set Interface,
	provides: set Interface
}{
	all t:Time | one c:Component | this in c.uses.t
	all t:Time | one c:Connector | this in c.outConnector.t
	all t:Time | one c:Connector | this in c.inConnector.t
	all t:Time | one i:Innovation | this in i.calledBy.t
	all t:Time | one i:Innovation | this in i.receivedBy.t
}

/**
 * A predicate to verify whether a component is deployed on at least one node at
 * a certain time.
 */
pred Component.isDeployed(t:Time) {
	some n:Node | this in n.hosts.t
}

pred Port.isDeployed(t:Time){
	some c:Component | this in c.uses.t
}

/**
 * Checks whether the component can intercept the specified invocation at time t.
 */
//pred Component.canIntercept(i:Invocation,t:Time) {
//	some c:Connector | this in c.connects.t and i in c.buffer.t
//}

/**
 * Connectors "wire" components together. A connector connects a number of components
 * at any one time instance. It buffers an amount of invocations that are being routed
 * between (not necessarily connected) components.
 */
sig Connector {
	// The set of ports connected by this connector
	inConnector: lone Port,
	// The set of ports connected by this connector
	outConnector: lone Port,
	// The set of invocations buffered by this connector
	buffer: set Invocation -> Time
}{
	// Connectors have to be supported by a physical communication path
	all disj c1,c2:Component,t:Time {
		c1 + c2 in connects.t implies
			some n1,n2:Node {
					c1 in n1.hosts.t
					c2 in n2.hosts.t
					n1 = n2 or some l:Link | n1+n2 in l.connects.t
			}
	}
}

/**
 * Once this connector connects a number of components, they remain connected.
 */
pred Connector.isReliable {
	all t:Time - TO/last | this.connects.t in this.connects.(t.next)
}

/**
 * This connector only connects components deployed on one (the local) host 
 * throughout its life time.
 */
pred Connector.isLocal {
	one n:Node { 
		all t:Time | all disj c1,c2:this.connects.t | c1 + c2 in n.hosts.t
	}
}

/**
 * A helper function to find connectors connecting the two specified components
 * at two specific times.
 */
fun getConnectors[c1:Component,c2:Component] : set Connector {
	{ c:Connector |
			some t1,t2:Time | c1 in c.connects.t1 and c2 in c.connects.t2
	}
}

/**
 * An invocation reifies the calling and executing of an operation. All invocations
 * uphold both invocation and execution semantics specified below.
 */
sig Invocation {
	// The invoked operation.
	of: lone Method,
	// The calling component.
	caller: lone Port,
	// The supposed receiving components.
	receivers: set Port,
	// The time at which the invocation is made (if any).
	invoked: lone Time,
	// The time at which the invocation is executed (if any).
	executed: lone Time
}{
	this.setup
	this.execute
}

/**
 * Invocation semantics.
 */
pred Invocation.setup {
	// If there is a time when this invocation is invoked, then...
	some this.invoked <=> {
		// The original calling component is connected to (at least) one connector 
		// to pass the invocation on. The invocation will only be buffered in one 
		// connector.
		let conn = { c:Connector | this.caller in c.connects.(this.invoked) } {
			// There is maximum one such connector...
			one c:conn {
				// There is a new corresponding invocation buffered by the connector.
				this in c.buffer.(this.invoked)
				(this.invoked) != TO/first => this not in c.buffer.((this.invoked).prev)
			}
		}
	}
}

/**
 * Execution semantics.
 */
pred Invocation.execute {
	    // If there is a time when this invocation is executed, then...
	some this.executed <=> {
		// Is this invocation actually invoked at some time before the execution time?
		some this.invoked and this.invoked.lte[this.executed]
		// There has to be one connector.
		one conn:Connector {
			// The invocation should be buffered in this connector.
			this in conn.buffer.(this.executed)
			// One corresponding invocation is removed from the connector buffer.
			this.executed != TO/last => this not in conn.buffer.((this.executed).next)
		}
	}
}


/**
 * The call predicate "creates" an invocation corresponding to the calling of operation op, 
 * with the specified details (calling component, intended receiving component, arguments, 
 * security principal associated to the invocation, invocation time).
 */
pred Invoke(callr:Component,recv:set Component,op:Method,arg:set univ,t_i:Time) {
	some inv:Invocation {
		inv.of = op
		inv.caller = callr
		inv.receivers = recv
		inv.invoked = t_i
	}
}

/**
 * The call predicate verifies whether an invocation corresponding to the calling of operation op, 
 * with the specified details (calling component, intended receiving component, arguments, 
 * security principal associated to the invocation, invocation time) exists.
 */
pred Invoked(callr:Component,recv:set Component,op:Method,arg:set univ,t_i:Time) {
	some inv:Invocation {
		inv.of = op
		inv.caller = callr
		recv in inv.receivers
		inv.invoked = t_i
	}
}

/**
 * The execute predicate is true if an invocation corresponding to the calling of operation op,
 * with the specified details (calling component, actual receiving component, arguments, 
 * security principal associated to the invocation, invocation time).
 */
pred Execute(callr:Component,recv:set Component,op:Method,arg:set univ,t_e:Time) {
	some inv:Invocation {
		inv.of = op
		inv.caller = callr
		recv in inv.receivers
		some c:Connector | inv in c.buffer.t_e and recv in c.connects.t_e
		inv.executed = t_e
	}
}


/*************************
 * Metamodel properties. *
 *************************/

/**
 * Typechecking ensures that operations are present at the receiving components
 * before an invocation is done. Without typechecking, the presence of the invoked
 * operation is only verified at execution time.
 */
pred TypeChecking {
	// For all invocations that are invoked,
	all i:Invocation | one i.invoked implies {
		// all receivers...
		all r:i.receivers {
			// ...offer the correct operation in at least one of their interfaces.
			some p:Port | r in p.provides and i.of in p.methods
		}
	}
}

/**
 * Small illustration where someone invokes the "buy" operation (without arguments), offered
 * by some "shop" component. Bob's computer, on which the browser is deployed, is
 * the client node. The shop is deployed on the server node. The buy-operation is
 * invoked at time "click".
 */
pred Show {
	one disj client,server:Node | one disj browser,shop:Port |
	 one buy:Method {
		one click:Time {
			one if:Interface | buy in if.methods 
			all t:Time | browser in client.hosts.t and shop in server.hosts.t
			Invoke[browser,shop,buy,none,click]
		}
	}
}

run Show for 2
