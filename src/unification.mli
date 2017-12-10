(** Unification variables are integers. *)
type variable    = int

(** We perform unification of first order terms, of type ['cons pterm]. 
    At this stage, the type of constructor is kept generic. 
    Typically, 'cons := string. *)
type 'cons pterm = ('cons, variable) Terms.t

(** Since everything is purely functional, we need to carry around
    a fresh name generator, [freshgen] *)
type freshgen = variable Utils.FreshGen.acc

(** [Mismatch] is raised whenever two terms are found that cannot be unified. *)
exception Mismatch of string

(* [Make] constructs an unification module given a module satisfying the [TermSig]
   signature. *)
module Make :
  functor (P : Types.S with type var = int) ->
  sig

    type term = P.t

    (* A [substitution] is a mapping of variables to terms. It is kept opaque, until required otherwise. *)
    type substitution

    type equations = (term * term) list

    (** An union-find tree. *)
    type uf = (term option, equations) UnionFind.t

    (** This sub-module is used when building the unification problem;
        it allows to accumulate equations in a pseudo-stately fashion. *)
    module Build :
    sig
      type build_env = {
        equations : equations;
        type_freshgen : freshgen;
      }
      val initial_build_env : build_env
      val fresh : build_env -> build_env * ('a, variable) Terms.t
      val join : build_env -> term -> term -> build_env
    end

    (** Solve unification problem. If everything goes well, yields an union-find tree. *)
    val unify : Build.build_env -> uf

    (** The read back phase turns the state of the union-find algorithm
        back into a most general unifier, that is, a mapping of variables
        to terms. This is essentially a graph traversal process,
        implemented using depth-first search. An acyclicity check is
        performed on the fly. *)
    val read_back : Build.build_env -> uf -> substitution

    (* Given a substitution, we can map terms to ground terms. *)
    val instantiate_term : substitution -> term -> term

  end
