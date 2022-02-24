using DataStructures
Var = UInt

struct Literal
    var::Var
    is_pos::Bool
end

LiteralIndex = UInt

@inline function number_to_literal(n::Int) Literal
    if n > 0
        Literal(n, true)
    else
        Literal(-n, false)
    end
end

@inline function literal_to_index(l::Literal) LiteralIndex
    2 * l.var - (l.is_pos ? 0 : 1)
end

@inline function index_to_literal(n::LiteralIndex) Literal
    Literal(div(n + 1, 2), n % 2 == 0)
end

function Base.show(io::IO, l::Literal)
    print(io, (l.is_pos ? "" : "¬") * string(Int(l.var)))
end

Clause = Set{Literal}
ClauseIndex = UInt

function Base.show(io::IO, c::Clause)
    print(io, "(" * join(c, " ⩔ ") * ")")
end

mutable struct Assignment
    is_pos::Bool
    decision_level::UInt
    antecedent::Union{ClauseIndex, Nothing}
end

INCREMENT_MULTIPLIER = 1.1
RESCALE_PERIOD = 500
DIVISOR = INCREMENT_MULTIPLIER ^ RESCALE_PERIOD
RANDOM_BRANCH_PERIOD = 200
mutable struct SATInstance
    clauses::Array{Clause}
    n_vars::UInt
    decision_level::UInt
    assignments::Array{Union{Assignment, Nothing}}
    decisions::Array{Var}
    watchlist::Array{LiteralIndex}
    watchers::Array{Dict{ClauseIndex, UInt}}
    activities::Array{Float64}
    n_conflicts::UInt
    bonus::Float64
end

function SATInstance(clauses::Array{Clause}, n_vars::UInt)
    assignments = Array{Union{Assignment, Nothing}}(nothing, n_vars)
    decisions = Var[]
    watchlist = LiteralIndex[] # set up later
    watchers = [Dict() for _ in 1:2 * n_vars]
    activities = Float64[0 for _ in 1:n_vars]

    SATInstance(clauses, n_vars, 0, assignments, decisions, watchlist, watchers, activities, 0, 0)
end

function load_sat(filename::String) SATInstance
    clauses::Array{Clause} = []
    n_vars = nothing
    open(filename) do f
        for (i, line) in enumerate(readlines(f))
            if length(line) == 0
                continue
            end
            tokens = split(line, " ")
            if tokens[1] == "c"
                continue
            end
            if tokens[1] == "p"
                if length(tokens) != 4
                    throw(LoadError(filename, i, "Incorrect p line"))
                end
                n_vars = parse(Var, tokens[3])
                continue
            end
            if tokens[length(tokens)] != "0"
                throw(LoadError(filename, i, "Expected 0 at the end of line"))
            end
            clause = Clause([number_to_literal(parse(Int, n)) for n in tokens[1:length(tokens)-1]])
            push!(clauses, clause)
        end
    end
    if n_vars === nothing
        throw(LoadError(filename, 0, "Never encountered p line"))
    end

    SATInstance(clauses, n_vars)
end

@inline function assign!(sat::SATInstance, var::Var, is_pos::Bool, antecedent::Union{ClauseIndex, Nothing}=nothing)
    sat.assignments[var] = Assignment(is_pos, sat.decision_level, antecedent)
    push!(sat.decisions, var)
end

function terminate(sat::SATInstance, is_sat::Bool) Bool
    if is_sat
        # make default assignmentse if SAT
        for (i, assignment) in enumerate(sat.assignments)
            if assignment === nothing
                sat.assignments[i] = Assignment(false, sat.decision_level, nothing)
            end
        end
    end

    @info "Terminating: " * (is_sat ? "SAT" : "UNSAT")
    is_sat
end

@inline function get_watchlist(c::Clause) Array{LiteralIndex}
    output = LiteralIndex[]
    for (i, literal) in enumerate(c)
        if i == 3
            break
        end
        push!(output, literal_to_index(literal))
    end

    output
end

function initialize_watchlist!(sat::SATInstance)
    sat.watchlist = LiteralIndex[0 for _ in 1:2*length(sat.clauses)]
    for (i, clause) in enumerate(sat.clauses)
        watch_1, watch_2 = get_watchlist(clause)
        sat.watchlist[2*i-1] = watch_1
        sat.watchers[watch_1][i] = 2

        sat.watchlist[2*i] = watch_2
        sat.watchers[watch_2][i] = 1
    end
end

function initialize_activities!(sat::SATInstance)
    for clause in sat.clauses
        for literal in clause
            sat.activities[literal.var] += 1
        end
    end
    sat.bonus = maximum(sat.activities) / 2
    sat.n_conflicts = 0
end


function simplify!(sat::SATInstance) Bool
    sat.decision_level = 0
    while true
        unit = get_unit(sat)
        
        
        if unit !== nothing
            # @debug "Assigning unit $(unit)"
            assign!(sat, unit.var, unit.is_pos)
            continue
        end

        pure = get_pure(sat)
        
        if pure !== nothing
            # @debug "Assigning pure $(pure)"
            assign!(sat, pure.var, pure.is_pos)
            continue
        end

        break
    end

    # simplify clauses by skipping satisfied clauses
    clauses = Clause[]
    for clause in sat.clauses
        is_sat = false
        new_clause = Clause()
        
        for literal in clause
            # only push unassigned vars
            if sat.assignments[literal.var] === nothing
                push!(new_clause, literal)
            elseif sat.assignments[literal.var].is_pos == literal.is_pos
                is_sat = true
                break
            end
        end
        # skip satisfied clauses
        if is_sat
            continue
        end
        if length(new_clause) == 0
            return terminate(sat, false)
        end
        push!(clauses, new_clause)
    end
    
    sat.clauses = clauses

    true
end

@inline function get_unit(sat::SATInstance) Union{Literal, Nothing}
    for clause in sat.clauses
        unit = get_clause_unit(sat, clause)
        
        if unit !== nothing
            return unit
        end
    end

    nothing
end

function get_clause_unit(sat::SATInstance, clause::Clause) Union{Literal, Nothing}
    unit = nothing
    for literal in clause
        # ignore satisfied clauses
        if sat.assignments[literal.var] !== nothing
            if sat.assignments[literal.var].is_pos == literal.is_pos
                return nothing
            end
        # if we find an unassigned var
        else
            if unit === nothing
                unit = literal
            else
                return nothing
            end
        end
    end

    unit
end

@inline function is_clause_sat(sat::SATInstance, clause::Clause) Bool
    for literal in clause
        if sat.assignments[literal.var] !== nothing && sat.assignments[literal.var].is_pos == literal.is_pos
            return true
        end
    end
    return false
end

function get_pure(sat::SATInstance) Union{Literal, Nothing}
    is_pure::Array{Tuple{Union{Bool, Nothing}, Union{Bool, Nothing}}} = [(nothing, nothing) for _ in 1:sat.n_vars]
    for clause in sat.clauses
        # ignore SAT clauses
        if is_clause_sat(sat, clause)
            continue
        end

    
        for literal in clause
            # ignore assigned vars
            if sat.assignments[literal.var] !== nothing
                continue
            end

            # first time seeing the literal: we have found a potential pure literal
            if is_pure[literal.var][1] === nothing
                is_pure[literal.var] = (true, literal.is_pos)
            # this has previously been a potential literal, but we have found a negated occurrence
            elseif is_pure[literal.var][1] && is_pure[literal.var][2] != literal.is_pos
                is_pure[literal.var] = (false, nothing)
            end
        end
    end

    for (var, (is_pure, is_pos)) in enumerate(is_pure)
        if is_pure === nothing || !is_pure
            continue
        end
        return Literal(var, is_pos)
    end
    
    nothing
end

function solve(sat::SATInstance) Bool
    @info "Simplifying expression with $(sat.n_vars) variables and $(length(sat.clauses)) clauses"

    if !simplify!(sat)
        return terminate(sat, false)
    end

    initialize_watchlist!(sat)
    initialize_activities!(sat)

    @info "Solving problem with $(length(filter(n -> n === nothing, sat.assignments))) variables and $(length(sat.clauses)) clauses"
    
    should_branch = true
    while true
        if should_branch && !decide!(sat)
            @info "Ran out of variables to assign"
            return terminate(sat, true)
        end

        conflict_clause = propagate!(sat)
        if conflict_clause === nothing
            should_branch = true
            continue
        end

        # learn form conflict
        learned_clause, encountered_vars::Set{Var} = learn(sat, conflict_clause)

        # if nothing can be learnt, then the instance is UNSAT
        if learned_clause === nothing
            @info "Cannot learn from conflict clause"
            return terminate(sat, false)
        end
        
        # @debug "Learned clause $(learned_clause)"
        should_branch = false  # force continued propagation
        sat.decision_level = compute_decision_level(sat, learned_clause)
        # @debug "Backtracking to decision level $(sat.decision_level)"
        backtrack!(sat)

        # if the clause has only one element, then we have backtracked to a state without any branching
        if length(learned_clause) === 1
            assignment = first(learned_clause)
            if sat.assignments[assignment.var] !== nothing && sat.assignments[assignment.var].is_pos != assignment.is_pos
                @info "Conflict at decision level 0"
                return terminate(sat, false)
            end

            assign!(sat, assignment.var, assignment.is_pos)
            continue
        end
        
        # learn the derived clause
        if !add_clause!(sat, learned_clause)
            @info "Learned clause has no UIP"
            terminate(sat, false)
        end

        # update activity scores
        update_activities!(sat, encountered_vars)
    end
end

@inline function decide!(sat::SATInstance) Bool
    literal = evsids(sat)
    if literal === nothing
        return false
    end
    
    sat.decision_level += 1
    # @debug "Deciding $(literal)"
    assign!(sat, literal.var, literal.is_pos)

    true
end

function evsids(sat::SATInstance) Union{Literal, Nothing}
    max_score = 0.0
    max_var::Union{Var, Nothing} = nothing
    for (i, score) in enumerate(sat.activities)
        if sat.assignments[i] !== nothing
            continue
        end

        if score > max_score
            max_var = i
            max_score = score
        end
    end
    if max_var === nothing
        return nothing
    end
    
    Literal(max_var, true)
end

function jeroslow_wang(sat::SATInstance) Union{Literal, Nothing}
    scores = Dict{Var, Float64}()
    for clause in sat.clauses
        # ignore SAT clauses
        is_clause_sat = false
        num_unassigned_vars = 0
        for literal in clause
            if sat.assignments[literal.var] === nothing
                num_unassigned_vars += 1
                continue
            end
            if sat.assignments[literal.var].is_pos == literal.is_pos
                is_clause_sat = true
                break
            end
        end
        if is_clause_sat
            continue
        end

        for literal in clause
            if sat.assignments[literal.var] === nothing
                scores[literal.var] = get(scores, literal.var, 0) + 1 / (1 << num_unassigned_vars)
            end
        end
    end
    
    # get max score variable
    max_score = 0.0
    max_var::Union{Var, Nothing} = nothing
    for (var, score) in scores
        if score > max_score
            max_var = var
            max_score = score
        end
    end 

    # if no assignment can be made, return
    if max_var === nothing
        return nothing
    end

    return Literal(max_var, true)
end

function propagate!(sat::SATInstance) Union{Clause, Nothing}
    # assignments is a stack
    assignments = Stack{Tuple{Literal, ClauseIndex}}()

    while true
        # check the last decision for watched literals
        decision = sat.decisions[length(sat.decisions)]

        # watchers index of the opposite literal
        watched_index = literal_to_index(Literal(
            decision, !sat.assignments[decision].is_pos
        ))
        
        for (clause_idx, which_watch) in copy(sat.watchers[watched_index])
            other_literal = index_to_literal(
                sat.watchlist[2*clause_idx - 2 + which_watch]
            )

            # quick check against the other watched literal in case it is assigned
            if sat.assignments[other_literal.var] !== nothing
                if sat.assignments[other_literal.var].is_pos == other_literal.is_pos
                    # clause is SAT
                    continue
                else
                    # clause is UNSAT
                    return sat.clauses[clause_idx]
                end
            end

            # we now know that the other watched literal isn't assigned
            replacement = nothing

            # see if there is some other unassigned literal we can watch
            for literal in sat.clauses[clause_idx]
                # ignore all falsified literals 
                if sat.assignments[literal.var] !== nothing
                    # if clause is SAT, just do nothing
                    if sat.assignments[literal.var].is_pos == literal.is_pos
                        replacement = literal
                        break
                    end
                    continue
                end
                # ignore the other literal
                if literal == other_literal
                    continue
                end
                # found a viable replacement!
                replacement = literal
                break
            end
            
            if replacement === nothing
                # unit clause!
                push!(assignments, (other_literal, clause_idx))
            else
                # found replacement; update watchlist
                replacement_index = literal_to_index(replacement)

                delete!(sat.watchers[watched_index], clause_idx)
                sat.watchers[replacement_index][clause_idx] = which_watch
                sat.watchlist[2*clause_idx+1-which_watch] = replacement_index
            end
        end
        
        # go through assignments and recursively propagate
        has_new_decision = false
        while length(assignments) > 0
            literal, antecedent = pop!(assignments)
        
            if sat.assignments[literal.var] === nothing
                assign!(sat, literal.var, literal.is_pos, antecedent)
                has_new_decision = true
                break
            end
        end
        if !has_new_decision
            break
        end
    end
    
    nothing
end

function learn(sat::SATInstance, conflict_clause::Clause) Union{Clause, Nothing}, Set{Var}
    # learn using first UIP

    learned_clause = copy(conflict_clause)
    encountered_variables = Set()
    # continuously resolve with antecedents of literals implied
    # at the current decision level until UIP
    last_level_literals = Stack{Literal}()

    for literal in learned_clause
        if sat.assignments[literal.var].decision_level != sat.decision_level
            continue
        end
        push!(last_level_literals, literal)
    end
    num_last_level_literals = length(last_level_literals)

    while num_last_level_literals > 1
        # this is in case we're at decision level 0 and have presolved antecedents
        if length(last_level_literals) == 0
            return nothing, encountered_variables
        end
        implied_literal = pop!(last_level_literals)

        # ignore literals assigned by branching
        if sat.assignments[implied_literal.var].antecedent === nothing
            continue
        end

        # resolve learned clause and implied literal's antecedent
        num_last_level_literals -= 1
        antecedent = sat.clauses[sat.assignments[implied_literal.var].antecedent]
        delete!(learned_clause, implied_literal)
        push!(encountered_variables, implied_literal.var)
        for literal in antecedent
            if literal in learned_clause || literal == Literal(implied_literal.var, !implied_literal.is_pos)
                continue
            end
            push!(learned_clause, literal)
            if sat.assignments[literal.var].decision_level == sat.decision_level
                push!(last_level_literals, literal)
                num_last_level_literals += 1
            end
        end
    end
    encountered_variables = union(encountered_variables, Set([l.var for l in learned_clause]))
    
    learned_clause, encountered_variables
end

@inline function compute_decision_level(sat::SATInstance, learned_clause::Clause) UInt
    max_level = 0
    for literal in learned_clause
        literal_decision_level = sat.assignments[literal.var].decision_level
        if literal_decision_level != sat.decision_level && literal_decision_level > max_level
            max_level = literal_decision_level
        end
    end

    max_level
end

@inline function backtrack!(sat::SATInstance)
    last_index = length(sat.decisions)
    while last_index > 0
        decision = sat.decisions[last_index]

        if sat.assignments[decision].decision_level == sat.decision_level
            break
        end

        sat.assignments[decision] = nothing
        last_index -= 1
    end
    sat.decisions = sat.decisions[1:last_index]
end

function add_clause!(sat::SATInstance, clause::Clause) Bool
    push!(sat.clauses, clause)

    # set up watched literals for the added clause and force unit propagation
    unit_literal::Union{Literal, Nothing} = nothing
    other_literal::Union{Literal, Nothing} = nothing
    for literal in clause
        if sat.assignments[literal.var] === nothing
            unit_literal = literal
        elseif sat.assignments[literal.var].decision_level == sat.decision_level
            other_literal = literal
        end
    end

    if unit_literal === nothing
        return false
    end

    unit_index = literal_to_index(unit_literal)
    other_index = literal_to_index(other_literal)
    push!(sat.watchlist, other_index)
    push!(sat.watchlist, unit_index)
    learned_clause_idx = UInt(length(sat.clauses))
    sat.watchers[unit_index][learned_clause_idx] = 1
    sat.watchers[other_index][learned_clause_idx] = 2
    assign!(sat, unit_literal.var, unit_literal.is_pos, learned_clause_idx)

    true
end

function update_activities!(sat::SATInstance, vars::Set{Var})
    for var in vars
        sat.activities[var] += sat.bonus
    end
    sat.n_conflicts += 1
    sat.bonus *= INCREMENT_MULTIPLIER

    # periodic decay
    if (sat.n_conflicts + 1) % RESCALE_PERIOD == 0
        sat.bonus /= DIVISOR
        for i in 1:length(sat.activities)
            sat.activities[i] /= DIVISOR
        end
    end
end

function verify(sat::SATInstance) Bool
    for clause in sat.clauses
        if !is_clause_sat(sat, clause)
            return false
        end
    end
    return true
end