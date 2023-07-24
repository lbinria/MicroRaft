package io.microraft.impl.util;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.SharedClock;

import java.io.IOException;
import java.util.HashMap;

public class SpecAccess {

    private static final HashMap<String, TraceInstrumentation> specs = new HashMap<>();

    public static TraceInstrumentation get(String name) {
        if (!specs.containsKey(name)) {
            try {
                specs.put(name, new TraceInstrumentation(name + ".ndjson", SharedClock.get("microraft.clock")));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        return specs.get(name);
    }

    public static VirtualField getStateVariable(String name) {
        return get(name).getVariable("state").getField(name);
    }

    public static VirtualField getCurrentTermVariable(String name) {
        return get(name).getVariable("currentTerm").getField(name);
    }

    public static VirtualField getLogVariable(String name) {
        return get(name).getVariable("log").getField(name);
    }

}
