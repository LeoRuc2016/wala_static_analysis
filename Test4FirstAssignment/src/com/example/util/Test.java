package com.example.util;

public class Test {
	String data;
	public Test(String d) {
		data = d;
	}
	public String processData(boolean b) {
		StringBuilder builder = new StringBuilder("Data = ");
		if (b) {
			builder.append(data);
		} else {
			builder.append("[data is not visible]");
		}
		builder.append("<DONE>");
		return builder.toString();
	}
}