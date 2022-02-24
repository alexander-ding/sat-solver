# stole this from http://www.sat4j.org/maven233/org.sat4j.core/xref/org/sat4j/minisat/restarts/LubyRestarts.html
mutable struct Luby
    un::UInt
    vn::UInt
    factor::UInt
end

function Luby(factor::UInt) Luby
    Luby(1, 1, factor)
end

function next!(l::Luby)
    if (l.un & -l.un) == l.vn
        l.un += 1
        l.vn = 1
    else
        l.vn = l.vn << 1
    end
end

function get(l::Luby) UInt
    l.vn * l.factor
end
