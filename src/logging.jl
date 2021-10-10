
using Logging
using Distributed

function log_fmt(level::LogLevel, _module, group, id, file, line)
    color, prefix, suffix = Logging.default_metafmt(level, _module, group, id, file, line)
    prefix = "Pid: $(myid()) " * prefix
    color, prefix, suffix
end

function init_logger()
    current_stream = Base.global_logger().stream
    Base.global_logger(Logging.ConsoleLogger(current_stream, meta_formatter=log_fmt))
end
