__precompile__()

import Dates
using ArgParse
using Base.Filesystem

include("Sat.jl")

function serialize(sat::SATInstance) String
    flags = []
    for (i, flag) in enumerate(sat.assignments)
        if flag === nothing
            throw(DomainError(sat.assignments, "Incomplete assignments"))
        end

        flag_str = flag.is_pos ? "true" : "false"
        push!(flags, "$(i) $(flag_str)")
    end

    join(flags, " ")
end

function parse_commandline()
    s = ArgParseSettings()
    @add_arg_table s begin
        "file"
            help = "CNF file"
            required = true
    end

    parse_args(s)
end

# function profile_test(sat::SATInstance)
#     solve(sat)
# end

# function profile(sat::SATInstance)
#     ProfileView.@profview profile_test(sat)
#     c = Condition()
#     wait(c)
#     exit()
# end

function main()
    parsed_args = parse_commandline()
    file = parsed_args["file"]
    @info "Loading file $(file) into a SAT instance"
    
    sat = load_sat(file)

    # profile(sat)

    start_time = Dates.now()
    is_sat = solve(sat)
    end_time = Dates.now()
    delta = round(Float64(Dates.value(end_time - start_time)) / 1000.0, digits=2)

    _, filename = splitdir(file)
    stem, _ = splitext(filename)
    
    if is_sat
        println("""{"Instance": "$(stem)", "Time": $(delta), "Result": "SAT", "Solution": "$(serialize(sat))"}""")

        if is_sat
            @assert verify(sat)
        end
    else
        println("""{"Instance": "$(stem)", "Time": $(delta), "Result": "UNSAT"}""")
    end
end
main()