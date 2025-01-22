import random
import pandas as pd
import itertools

def generator(sig, out, seed, i=10, e=None, q=20, r=0.2, length=300, int_range = None):
    """
    Generate a random log for the given signature.
    
    - sig: signature
    - i: Index rate (time-points pr time-stamp).
    - e: Event rate (events pr time-stamp).
    - q: Number of most recently sampled unique data values.
    - r: Probability to sample a fresh data value.
    - length: Total time-wise length of the log.
    - int_range: Range of data values.
    """
    random.seed(seed)

    # Initialize the recently used data values
    if int_range is None:
        int_range = (100000000,1000000000)
    data_value_cache = []
    for _ in range(q):
        data_value_cache.append(random.randrange(int_range[0], int_range[1]))

    if e is None or e < i:
        e = i
    events = []
    tp = 0
    for time_stamp in range(0, length):
        for _ in range(i):
            for _ in range(e//i):
                # Randomly select predicate
                event_type = random.choice(sig.predicates)

                arg_values = []
                for _ in range(event_type.len):
                    if random.random() < r:
                        # Generate a fresh data value
                        data_value = random.randrange(int_range[0], int_range[1])
                        data_value_cache.append(data_value)

                        if len(data_value_cache) > q:
                            data_value_cache.pop(0)
                    else:
                        data_value = random.choice(data_value_cache)
                    arg_values.append(f"x{len(arg_values)}={data_value}")

                event = {
                    'eventtype': event_type.name,
                    'time-point': f"tp={tp}",
                    'time-stamp': f"ts={time_stamp}"
                }

                for idx, arg_value in enumerate(arg_values):
                    event[f'arg{idx}'] = arg_value

                events.append(event)
            tp += 1

    # Create DataFrame
    df = pd.DataFrame(data = events)
    # Write to file without trailing commas
    out = out.replace('.csv','').replace('.log','')
    with open(out+'.csv', "w+") as f:
        f.write("\n".join([l.strip(", ") for l in df.to_csv(index=False, header=None).split("\n")]))
    convert_csv_to_log(out+'.csv', out+'.log')

def convert_csv_to_log(input_csv_path, output_log_path):
    # Dictionary to group events by timestamp
    events_by_timestamp = {}

    with open(input_csv_path, mode='r') as csv_file:
        for row in csv_file:
            row = row.strip().split(',')
            eventtype = row[0].strip()
            timepoint = row[1].strip().replace('tp=', '')
            timestamp = row[2].strip().replace('ts=', '')
            # Collect argument values
            args = []
            for i in range(3, len(row)):
                arg_raw = row[i].strip()
                if arg_raw:
                    splitted = arg_raw.split('=')
                    if len(splitted) == 2:
                        _, val = splitted
                        args.append(val.strip())
            if args:
                event_str = (eventtype, ','.join(args))
            else:
                event_str = (eventtype, '')

            # Group events by timestamp in the dictionary
            if timestamp not in events_by_timestamp:
                events_by_timestamp[timestamp] = {}
                events_by_timestamp[timestamp][timepoint] = [event_str]
            else:
                if timepoint not in events_by_timestamp[timestamp]:
                    events_by_timestamp[timestamp][timepoint] = [event_str]
                else:
                    events_by_timestamp[timestamp][timepoint].append(event_str)

    # write to output
    with open(output_log_path, mode='w+') as log_file:
        try:
            for ts in sorted(events_by_timestamp.keys(), key=lambda x: float(x)):
                for timepoint, events in events_by_timestamp[ts].items():
                    line_str = f"@{ts} "
                    a = itertools.groupby(sorted(events, key=lambda x: x[0]), lambda x: x[0])
                    for key, subiter in a:

                        line_str += f"{key}{''.join(f'({item[1]})' for item in subiter)} "
                    # events_list = sorted(set(event[0] for event in events))
                    # event_dir = {}

                    log_file.write(line_str[:-1] + ";\n")
        except ValueError:
            print(events_by_timestamp.keys())
