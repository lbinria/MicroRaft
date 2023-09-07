package io.microraft.tlavalidation.models;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.lbee.instrumentation.TLASerializer;

public class Entry implements TLASerializer {

    private final long term;
    private final String val;

    public Entry(long term, String val) {
        this.term = term;
        this.val = val;
    }

    public Entry(JsonObject jsonObject) {
        this.term = jsonObject.get("term").getAsInt();
        this.val = jsonObject.get("val").getAsString();
    }

    public long getTerm() {
        return term;
    }

    public String getVal() {
        return val;
    }

    public JsonElement toJson() {
        return tlaSerialize();
    }

    @Override
    public JsonElement tlaSerialize() {
        final JsonObject jsonObject = new JsonObject();
        jsonObject.addProperty("term", term);
        jsonObject.addProperty("val", val);
        return jsonObject;
    }

    @Override
    public String toString() {
        return tlaSerialize().toString();
    }
}
