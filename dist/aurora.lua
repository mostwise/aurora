--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 216) then
					if (Enum <= 107) then
						if (Enum <= 53) then
							if (Enum <= 26) then
								if (Enum <= 12) then
									if (Enum <= 5) then
										if (Enum <= 2) then
											if (Enum <= 0) then
												local A;
												Stk[Inst[2]] = {};
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												if (Stk[Inst[2]] ~= Inst[4]) then
													VIP = VIP + 1;
												else
													VIP = Inst[3];
												end
											elseif (Enum == 1) then
												Stk[Inst[2]] = #Stk[Inst[3]];
											else
												local A;
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Unpack(Stk, A + 1, Inst[3]));
												VIP = VIP + 1;
												Inst = Instr[VIP];
												do
													return Stk[Inst[2]];
												end
												VIP = VIP + 1;
												Inst = Instr[VIP];
												do
													return;
												end
											end
										elseif (Enum <= 3) then
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											do
												return Stk[A](Unpack(Stk, A + 1, Inst[3]));
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											do
												return Unpack(Stk, A, Top);
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum > 4) then
											Stk[Inst[2]][Inst[3]] = Inst[4];
										else
											local B;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										end
									elseif (Enum <= 8) then
										if (Enum <= 6) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
										elseif (Enum == 7) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = -Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = -Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
										else
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = #Stk[Inst[3]];
										end
									elseif (Enum <= 10) then
										if (Enum > 9) then
											local B;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										else
											local Edx;
											local Results, Limit;
											local A;
											A = Inst[2];
											Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
											Top = (Limit + A) - 1;
											Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Top));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results, Limit = _R(Stk[A](Stk[A + 1]));
											Top = (Limit + A) - 1;
											Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = -Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										end
									elseif (Enum > 11) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 19) then
									if (Enum <= 15) then
										if (Enum <= 13) then
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
										elseif (Enum > 14) then
											if (Inst[2] < Stk[Inst[4]]) then
												VIP = Inst[3];
											else
												VIP = VIP + 1;
											end
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 17) then
										if (Enum > 16) then
											local A = Inst[2];
											local B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										else
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Enum == 18) then
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									else
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 22) then
									if (Enum <= 20) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									elseif (Enum == 21) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
									end
								elseif (Enum <= 24) then
									if (Enum > 23) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Inst[2] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum == 25) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 39) then
								if (Enum <= 32) then
									if (Enum <= 29) then
										if (Enum <= 27) then
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										elseif (Enum > 28) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										else
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 30) then
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									elseif (Enum > 31) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum <= 35) then
									if (Enum <= 33) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									elseif (Enum == 34) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 37) then
									if (Enum > 36) then
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum == 38) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 46) then
								if (Enum <= 42) then
									if (Enum <= 40) then
										local Step;
										local Index;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Index = Stk[A];
										Step = Stk[A + 2];
										if (Step > 0) then
											if (Index > Stk[A + 1]) then
												VIP = Inst[3];
											else
												Stk[A + 3] = Index;
											end
										elseif (Index < Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Enum > 41) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 44) then
									if (Enum > 43) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum > 45) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 49) then
								if (Enum <= 47) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = not Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 48) then
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
								end
							elseif (Enum <= 51) then
								if (Enum == 50) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum > 52) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 80) then
							if (Enum <= 66) then
								if (Enum <= 59) then
									if (Enum <= 56) then
										if (Enum <= 54) then
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
										elseif (Enum > 55) then
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
										end
									elseif (Enum <= 57) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									elseif (Enum > 58) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum <= 62) then
									if (Enum <= 60) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									elseif (Enum == 61) then
										Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
									else
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									end
								elseif (Enum <= 64) then
									if (Enum == 63) then
										local B;
										local A;
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum == 65) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 73) then
								if (Enum <= 69) then
									if (Enum <= 67) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum == 68) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = -Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									else
										local A;
										Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 71) then
									if (Enum > 70) then
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = not Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum == 72) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 76) then
								if (Enum <= 74) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 75) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 78) then
								if (Enum > 77) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum > 79) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 93) then
							if (Enum <= 86) then
								if (Enum <= 83) then
									if (Enum <= 81) then
										local A = Inst[2];
										local Step = Stk[A + 2];
										local Index = Stk[A] + Step;
										Stk[A] = Index;
										if (Step > 0) then
											if (Index <= Stk[A + 1]) then
												VIP = Inst[3];
												Stk[A + 3] = Index;
											end
										elseif (Index >= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Enum > 82) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum <= 84) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 85) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local T;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 89) then
								if (Enum <= 87) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 88) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 91) then
								if (Enum == 90) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 92) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 100) then
							if (Enum <= 96) then
								if (Enum <= 94) then
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum == 95) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum <= 98) then
								if (Enum > 97) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 99) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 103) then
							if (Enum <= 101) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 102) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 105) then
							if (Enum == 104) then
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 106) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = not Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 161) then
						if (Enum <= 134) then
							if (Enum <= 120) then
								if (Enum <= 113) then
									if (Enum <= 110) then
										if (Enum <= 108) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										elseif (Enum > 109) then
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 111) then
										local B;
										local A;
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									elseif (Enum == 112) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 116) then
									if (Enum <= 114) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									elseif (Enum == 115) then
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum <= 118) then
									if (Enum > 117) then
										Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum > 119) then
									local B;
									local A;
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum <= 127) then
								if (Enum <= 123) then
									if (Enum <= 121) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 122) then
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 125) then
									if (Enum > 124) then
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum == 126) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 130) then
								if (Enum <= 128) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum == 129) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 132) then
								if (Enum == 131) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = -Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = -Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum > 133) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 147) then
							if (Enum <= 140) then
								if (Enum <= 137) then
									if (Enum <= 135) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 136) then
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 138) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 139) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 143) then
								if (Enum <= 141) then
									local B;
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum > 142) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 145) then
								if (Enum == 144) then
									local T;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									for Idx = A + 1, Top do
										Insert(T, Stk[Idx]);
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum == 146) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 154) then
							if (Enum <= 150) then
								if (Enum <= 148) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 149) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 152) then
								if (Enum > 151) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum > 153) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 157) then
							if (Enum <= 155) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 156) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 159) then
							if (Enum > 158) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 160) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local T;
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							for Idx = A + 1, Top do
								Insert(T, Stk[Idx]);
							end
						end
					elseif (Enum <= 188) then
						if (Enum <= 174) then
							if (Enum <= 167) then
								if (Enum <= 164) then
									if (Enum <= 162) then
										local B;
										local Edx;
										local Results, Limit;
										local A;
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									elseif (Enum == 163) then
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 165) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum > 166) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 170) then
								if (Enum <= 168) then
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								elseif (Enum == 169) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 172) then
								if (Enum > 171) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 173) then
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 181) then
							if (Enum <= 177) then
								if (Enum <= 175) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								elseif (Enum == 176) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 179) then
								if (Enum > 178) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum > 180) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 184) then
							if (Enum <= 182) then
								local A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
							elseif (Enum > 183) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 186) then
							if (Enum == 185) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum > 187) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 202) then
						if (Enum <= 195) then
							if (Enum <= 191) then
								if (Enum <= 189) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 190) then
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 193) then
								if (Enum == 192) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum > 194) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
							end
						elseif (Enum <= 198) then
							if (Enum <= 196) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 197) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 200) then
							if (Enum > 199) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 201) then
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 209) then
						if (Enum <= 205) then
							if (Enum <= 203) then
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 204) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 207) then
							if (Enum > 206) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 208) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 212) then
						if (Enum <= 210) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum == 211) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 280) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 214) then
						if (Enum > 213) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum == 215) then
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return Stk[Inst[2]];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 324) then
					if (Enum <= 270) then
						if (Enum <= 243) then
							if (Enum <= 229) then
								if (Enum <= 222) then
									if (Enum <= 219) then
										if (Enum <= 217) then
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										elseif (Enum == 218) then
											local Edx;
											local Results, Limit;
											local B;
											local A;
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results, Limit = _R(Stk[A](Stk[A + 1]));
											Top = (Limit + A) - 1;
											Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Top));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
										else
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return Stk[Inst[2]];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum <= 220) then
										local K;
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 221) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local B;
										local Edx;
										local Results, Limit;
										local A;
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									end
								elseif (Enum <= 225) then
									if (Enum <= 223) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									elseif (Enum == 224) then
										local K;
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 227) then
									if (Enum == 226) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum > 228) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 236) then
								if (Enum <= 232) then
									if (Enum <= 230) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 231) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum <= 234) then
									if (Enum > 233) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
									end
								elseif (Enum == 235) then
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] <= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 239) then
								if (Enum <= 237) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								elseif (Enum > 238) then
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 241) then
								if (Enum > 240) then
									local A = Inst[2];
									local Results = {Stk[A]()};
									local Limit = Inst[4];
									local Edx = 0;
									for Idx = A, Limit do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum > 242) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 256) then
							if (Enum <= 249) then
								if (Enum <= 246) then
									if (Enum <= 244) then
										local K;
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 245) then
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum <= 247) then
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum > 248) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 252) then
								if (Enum <= 250) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 251) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 254) then
								if (Enum > 253) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 255) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 263) then
							if (Enum <= 259) then
								if (Enum <= 257) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								elseif (Enum == 258) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3] / Stk[Inst[4]];
								end
							elseif (Enum <= 261) then
								if (Enum > 260) then
									local A;
									local K;
									local B;
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum > 262) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 266) then
							if (Enum <= 264) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 265) then
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 268) then
							if (Enum > 267) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum > 269) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 297) then
						if (Enum <= 283) then
							if (Enum <= 276) then
								if (Enum <= 273) then
									if (Enum <= 271) then
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 272) then
										if (Inst[2] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum <= 274) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 275) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 279) then
								if (Enum <= 277) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 278) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								end
							elseif (Enum <= 281) then
								if (Enum > 280) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum > 282) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 290) then
							if (Enum <= 286) then
								if (Enum <= 284) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 285) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 288) then
								if (Enum > 287) then
									Stk[Inst[2]] = Env[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								end
							elseif (Enum > 289) then
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 293) then
							if (Enum <= 291) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum == 292) then
								do
									return;
								end
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 295) then
							if (Enum == 294) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum > 296) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 310) then
						if (Enum <= 303) then
							if (Enum <= 300) then
								if (Enum <= 298) then
									Stk[Inst[2]] = {};
								elseif (Enum == 299) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 301) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 302) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 306) then
							if (Enum <= 304) then
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							elseif (Enum > 305) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 308) then
							if (Enum > 307) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 309) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 317) then
						if (Enum <= 313) then
							if (Enum <= 311) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 312) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 315) then
							if (Enum == 314) then
								do
									return Stk[Inst[2]]();
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum > 316) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local B;
							local Edx;
							local Results, Limit;
							local A;
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 320) then
						if (Enum <= 318) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 319) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 322) then
						if (Enum > 321) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum > 323) then
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 378) then
					if (Enum <= 351) then
						if (Enum <= 337) then
							if (Enum <= 330) then
								if (Enum <= 327) then
									if (Enum <= 325) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 326) then
										if (Stk[Inst[2]] > Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 328) then
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum > 329) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 333) then
								if (Enum <= 331) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = not Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 332) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 335) then
								if (Enum == 334) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 336) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 344) then
							if (Enum <= 340) then
								if (Enum <= 338) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								elseif (Enum == 339) then
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 342) then
								if (Enum == 341) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum > 343) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 347) then
							if (Enum <= 345) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 346) then
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 349) then
							if (Enum == 348) then
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 350) then
							Stk[Inst[2]]();
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 364) then
						if (Enum <= 357) then
							if (Enum <= 354) then
								if (Enum <= 352) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 353) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 355) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Enum == 356) then
								local Edx;
								local Results;
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 360) then
							if (Enum <= 358) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum > 359) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 362) then
							if (Enum > 361) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 363) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							local B;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 371) then
						if (Enum <= 367) then
							if (Enum <= 365) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 366) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 369) then
							if (Enum == 368) then
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum == 370) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 374) then
						if (Enum <= 372) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 373) then
							local B;
							local A;
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Step;
							local Index;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Index = Stk[A];
							Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 376) then
						if (Enum == 375) then
							if (Stk[Inst[2]] > Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = VIP + Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum == 377) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = not Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Top do
							Insert(T, Stk[Idx]);
						end
					end
				elseif (Enum <= 405) then
					if (Enum <= 391) then
						if (Enum <= 384) then
							if (Enum <= 381) then
								if (Enum <= 379) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum == 380) then
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
								end
							elseif (Enum <= 382) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 383) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 387) then
							if (Enum <= 385) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 386) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local B;
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 389) then
							if (Enum > 388) then
								Stk[Inst[2]] = -Stk[Inst[3]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum > 390) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 398) then
						if (Enum <= 394) then
							if (Enum <= 392) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 393) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 396) then
							if (Enum == 395) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 397) then
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 401) then
						if (Enum <= 399) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 400) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
						end
					elseif (Enum <= 403) then
						if (Enum > 402) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
						end
					elseif (Enum > 404) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						local B;
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 419) then
					if (Enum <= 412) then
						if (Enum <= 408) then
							if (Enum <= 406) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 407) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 410) then
							if (Enum == 409) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum > 411) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 415) then
						if (Enum <= 413) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 414) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 417) then
						if (Enum == 416) then
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum > 418) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					else
						local Edx;
						local Results;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 426) then
					if (Enum <= 422) then
						if (Enum <= 420) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 421) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 424) then
						if (Enum == 423) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A = Inst[2];
							local Cls = {};
							for Idx = 1, #Lupvals do
								local List = Lupvals[Idx];
								for Idz = 0, #List do
									local Upv = List[Idz];
									local NStk = Upv[1];
									local DIP = Upv[2];
									if ((NStk == Stk) and (DIP >= A)) then
										Cls[DIP] = NStk[DIP];
										Upv[1] = Cls;
									end
								end
							end
						end
					elseif (Enum == 425) then
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						do
							return Stk[Inst[2]];
						end
					end
				elseif (Enum <= 429) then
					if (Enum <= 427) then
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					elseif (Enum == 428) then
						local T;
						local A;
						local K;
						local B;
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						T = Stk[A];
						B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 431) then
					if (Enum > 430) then
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						local Edx;
						local Results, Limit;
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum == 432) then
					local A;
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					do
						return Unpack(Stk, A, Top);
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					do
						return;
					end
				else
					local A;
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = {};
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = {};
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					do
						return Unpack(Stk, A, Top);
					end
					VIP = VIP + 1;
					Inst = Instr[VIP];
					do
						return;
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!213Q00030B3Q00636F72652F5369676E616C03093Q00636F72652F4D61696403093Q00636F72652F5574696C030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030A3Q00636F72652F476C797068030D3Q00636F72652F506C6174666F726D030A3Q00636F72652F466C616773030B3Q00636F72652F486F746B657903093Q00636F72652F44726167030E3Q006F7665726C6179732F4C6179657203113Q00636F6D706F6E656E74732F57696E646F77030E3Q00636F6D706F6E656E74732F54616203133Q00636F6D706F6E656E74732F47726F7570626F7803113Q00636F6D706F6E656E74732F546F2Q676C6503113Q00636F6D706F6E656E74732F536C6964657203133Q00636F6D706F6E656E74732F44726F70646F776E03143Q00636F6D706F6E656E74732F4B65795069636B657203163Q00636F6D706F6E656E74732F436F6C6F725069636B657203113Q00636F6D706F6E656E74732F42752Q746F6E03103Q00636F6D706F6E656E74732F496E70757403103Q00636F6D706F6E656E74732F4C6162656C03123Q00636F6D706F6E656E74732F4469766964657203153Q006F7665726C6179732F4E6F74696669636174696F6E030F3Q006F7665726C6179732F4469616C6F6703103Q006F7665726C6179732F542Q6F6C74697003123Q006F7665726C6179732F57617465726D61726B03143Q006F7665726C6179732F4B657962696E644C697374030F3Q006F7665726C6179732F53656172636803143Q006D616E61676572732F536176654D616E6167657203153Q006D616E61676572732F5468656D654D616E6167657203043Q00696E6974004E4Q002A017Q002A2Q015Q0006D400023Q000100032Q0018012Q00014Q0018017Q0018012Q00023Q000290010300013Q0010563Q00010003000290010300023Q0010563Q00020003000290010300033Q0010563Q00030003000290010300043Q0010563Q00040003000290010300053Q0010563Q00050003000290010300063Q0010563Q00060003000290010300073Q0010563Q00070003000290010300083Q0010563Q00080003000290010300093Q0010563Q000900030002900103000A3Q0010563Q000A00030002900103000B3Q0010563Q000B00030002900103000C3Q0010563Q000C00030002900103000D3Q0010563Q000D00030002900103000E3Q0010563Q000E00030002900103000F3Q0010563Q000F0003000290010300103Q0010563Q00100003000290010300113Q0010563Q00110003000290010300123Q0010563Q00120003000290010300133Q0010563Q00130003000290010300143Q0010563Q00140003000290010300153Q0010563Q00150003000290010300163Q0010563Q00160003000290010300173Q0010563Q00170003000290010300183Q0010563Q00180003000290010300193Q0010563Q001900030002900103001A3Q0010563Q001A00030002900103001B3Q0010563Q001B00030002900103001C3Q0010563Q001C00030002900103001D3Q0010563Q001D00030002900103001E3Q0010563Q001E00030002900103001F3Q0010563Q001F0003000290010300203Q0010563Q00200003000290010300213Q0010563Q002100032Q0018010300023Q001291000400214Q00890003000200022Q003A010300014Q003500036Q0024012Q00013Q00223Q00053Q00026Q00F03F03053Q00652Q726F7203173Q004175726F72613A206D692Q73696E67206D6F64756C652003083Q00746F737472696E67027Q004001214Q007000016Q00162Q0100013Q0006930001000600013Q00049F012Q000600010020100102000100012Q00AA010200024Q0070000200014Q0016010200023Q0006FC000200120001000100049F012Q00120001001220010300023Q0012D1000400033Q00122Q000500046Q00068Q0005000200024Q00040004000500122Q000500056Q0003000500012Q007000036Q002A010400014Q001E000500054Q00250004000100012Q004A01033Q00042Q0018010300024Q0070000400024Q00890003000200022Q007000046Q002A010500014Q0018010600034Q00250005000100012Q004A01043Q00052Q00AA010300024Q0024012Q00017Q000B3Q0003073Q002Q5F696E646578030A3Q00446973636F2Q6E656374030A3Q00646973636F2Q6E65637403073Q0044657374726F792Q033Q006E657703073Q00436F2Q6E65637403073Q00636F2Q6E65637403043Q004F6E636503043Q0046697265030D3Q00446973636F2Q6E656374412Q6C03053Q00436F756E74011E4Q002A2Q015Q0010560001000100012Q002A01025Q00105600020001000200029001035Q00102301020002000300202Q00030002000200102Q00020003000300202Q00030002000200102Q0002000400030006D400030001000100012Q0018012Q00013Q0010560001000500030006D400030002000100012Q0018012Q00023Q001056000100060003002010010300010006001056000100070003000290010300033Q001056000100080003000290010300043Q001056000100090003000290010300053Q0010560001000A000300201001030001000A001056000100040003000290010300063Q0010560001000B00032Q00AA2Q0100024Q0024012Q00013Q00073Q00093Q0003093Q00436F2Q6E6563746564010003073Q005F7369676E616C03093Q005F68616E646C657273026Q00F03F03053Q007461626C6503063Q0072656D6F76652Q033Q005F666E0001173Q0020102Q013Q00010006FC000100040001000100049F012Q000400012Q0024012Q00013Q0030053Q000100020020102Q013Q00030020102Q0100010004001291000200054Q0001000300013Q001291000400053Q0004F30002001500012Q001601060001000500066A0106001400013Q00049F012Q00140001001220010600063Q0020100106000600072Q0018010700014Q0018010800054Q004D01060008000100049F012Q001500010004510002000B00010030053Q000800092Q0024012Q00017Q00023Q00030C3Q007365746D6574617461626C6503093Q005F68616E646C65727300083Q0012B1012Q00016Q00013Q00014Q00025Q00102Q0001000200024Q00029Q0000029Q008Q00017Q000D3Q0003043Q007479706503083Q0066756E6374696F6E03053Q00652Q726F7203273Q005369676E616C3A436F2Q6E656374206578706563747320612066756E6374696F6E2C20676F7420027Q0040030C3Q007365746D6574617461626C6503073Q005F7369676E616C2Q033Q005F666E03093Q00436F2Q6E65637465642Q0103053Q007461626C6503063Q00696E7365727403093Q005F68616E646C657273021B3Q001220010200014Q0018010300014Q00890002000200020026960002000D0001000200049F012Q000D0001001220010200033Q0012D1000300043Q00122Q000400016Q000500016Q0004000200024Q00030003000400122Q000400056Q000200040001001220010200064Q002A01033Q0003001056000300073Q00105600030008000100300500030009000A2Q007000046Q008C0102000400020012200103000B3Q00202C00030003000C00202Q00043Q000D4Q000500026Q0003000500014Q000200028Q00017Q00013Q0003073Q00436F2Q6E65637402083Q00201100033Q00010006D400053Q000100022Q0018012Q00024Q0018012Q00014Q008C0103000500022Q0018010200034Q00AA010200024Q0024012Q00013Q00013Q00013Q00030A3Q00446973636F2Q6E65637400074Q007000015Q0020110001000100012Q00042Q01000200012Q0070000100014Q003001026Q00612Q013Q00012Q0024012Q00017Q00043Q0003093Q005F68616E646C657273026Q00F03F03093Q00436F2Q6E65637465642Q033Q005F666E01173Q00201001023Q00012Q002A01036Q0001000400023Q001291000500024Q0018010600043Q001291000700023Q0004F30005000A00012Q00160109000200082Q004A010300080009000451000500070001001291000500024Q0018010600043Q001291000700023Q0004F30005001600012Q0016010900030008002010010A00090003000693000A001500013Q00049F012Q00150001002010010A000900042Q0030010B6Q0061010A3Q00010004510005000E00012Q0024012Q00017Q00073Q0003093Q005F68616E646C657273026Q00F03F026Q00F0BF03093Q00436F2Q6E656374656401002Q033Q005F666E00010C3Q0020102Q013Q00012Q0001000200013Q001291000300023Q001291000400033Q0004F30002000B00012Q00160106000100050030050006000400052Q00160106000100050030050006000600070020F90001000500070004510002000500012Q0024012Q00017Q00013Q0003093Q005F68616E646C65727301043Q0020102Q013Q00012Q0001000100014Q00AA2Q0100024Q0024012Q00017Q000A3Q0003073Q002Q5F696E6465782Q033Q006E657703043Q004769766503083Q00476976655461736B2Q033Q00412Q6403073Q0047697665412Q6C030A3Q00446F436C65616E696E6703073Q0044657374726F7903053Q00436C65616E03053Q00436F756E7401194Q002A2Q015Q0010560001000100010006D400023Q000100012Q0018012Q00013Q001056000100020002000290010200013Q0010232Q010003000200202Q00020001000300102Q00010004000200202Q00020001000300102Q000100050002000290010200023Q001056000100060002000290010200033Q0006D400030004000100012Q0018012Q00023Q0010232Q010007000300202Q00030001000700102Q00010008000300202Q00030001000700102Q000100090003000290010300053Q0010560001000A00032Q00AA2Q0100024Q0024012Q00013Q00063Q00043Q00030C3Q007365746D6574617461626C6503063Q005F7461736B7303093Q005F636C65616E696E67012Q00093Q001220012Q00014Q002A2Q013Q00022Q002A01025Q0010560001000200020030050001000300042Q007000026Q0056012Q00024Q00358Q0024012Q00017Q00044Q0003053Q007461626C6503063Q00696E7365727403063Q005F7461736B73020B3Q002647000100040001000100049F012Q000400012Q001E000200024Q00AA010200023Q001220010200023Q00202C00020002000300202Q00033Q00044Q000400016Q0002000400014Q000100028Q00017Q00023Q0003063Q0069706169727303043Q0047697665020B3Q001220010200014Q0018010300014Q005E00020002000400049F012Q0007000100201100073Q00022Q0018010900064Q004D010700090001000677000200040001000200049F012Q000400012Q00AA2Q0100024Q0024012Q00017Q00083Q0003043Q007479706503083Q0066756E6374696F6E03053Q007461626C6503083Q00757365726461746103073Q0044657374726F79030A3Q00446F436C65616E696E67030A3Q00446973636F2Q6E656374030A3Q00646973636F2Q6E656374012D3Q0012202Q0100014Q001801026Q0089000100020002002647000100080001000200049F012Q000800012Q001801026Q005E0102000100012Q0024012Q00013Q0026960001000C0001000300049F012Q000C00010026470001002C0001000400049F012Q002C0001001220010200013Q00201001033Q00052Q0089000200020002002647000200140001000200049F012Q0014000100201100023Q00052Q000401020002000100049F012Q002B0001001220010200013Q00201001033Q00062Q00890002000200020026470002001C0001000200049F012Q001C000100201100023Q00062Q000401020002000100049F012Q002B0001001220010200013Q00201001033Q00072Q0089000200020002002647000200240001000200049F012Q0024000100201100023Q00072Q000401020002000100049F012Q002B0001001220010200013Q00201001033Q00082Q00890002000200020026470002002B0001000200049F012Q002B000100201100023Q00082Q00040102000200012Q0024012Q00014Q0024012Q00017Q000B3Q0003093Q005F636C65616E696E672Q0103063Q005F7461736B73026Q00F03F026Q00F0BF03053Q007063612Q6C03043Q007761726E03183Q005B4175726F72615D20636C65616E757020652Q726F723A2003083Q00746F737472696E67000100011D3Q0020102Q013Q00010006930001000400013Q00049F012Q000400012Q0024012Q00013Q0030053Q000100020020102Q013Q00032Q002A01025Q0010563Q000300022Q0001000200013Q001291000300043Q001291000400053Q0004F30002001B0001001220010600064Q007000076Q00160108000100052Q00270006000800070006FC000600190001000100049F012Q00190001001220010800073Q001280000900083Q00122Q000A00096Q000B00076Q000A000200024Q00090009000A4Q0008000200010020F900010005000A0004510002000C00010030053Q0001000B2Q0024012Q00017Q00013Q0003063Q005F7461736B7301043Q0020102Q013Q00012Q0001000100014Q00AA2Q0100024Q0024012Q00017Q00293Q0003053Q00636C616D7003043Q006C65727003053Q00726F756E6403063Q00666F726D61742Q033Q006D617003053Q0066752Q7A79030A3Q00686578546F436F6C6F72030A3Q00636F6C6F72546F48657803083Q00642Q6570436F707903053Q00636F756E7403073Q00696E6465784F66030A3Q00736F727465644B65797303093Q004C656674536869667403063Q004C5348494654030A3Q005269676874536869667403063Q00525348494654030B3Q004C656674436F6E74726F6C03053Q004C4354524C030C3Q005269676874436F6E74726F6C03053Q00524354524C03073Q004C656674416C7403043Q004C414C5403083Q005269676874416C7403043Q0052414C54030C3Q004D6F75736542752Q746F6E3103063Q004D4F55534531030C3Q004D6F75736542752Q746F6E3203063Q004D4F55534532030C3Q004D6F75736542752Q746F6E3303063Q004D4F5553453303093Q004261636B71756F746503013Q006003063Q0052657475726E03053Q00454E54455203063Q004573636170652Q033Q0045534303053Q00537061636503053Q00535041434503073Q00556E6B6E6F776E03043Q006E6F6E6503073Q006B65794E616D65012F4Q002A2Q015Q00029001025Q001056000100010002000290010200013Q001056000100020002000290010200023Q001056000100030002000290010200033Q001056000100040002000290010200043Q001056000100050002000290010200053Q001056000100060002000290010200063Q0010560001000700020006D400020007000100012Q0018012Q00013Q0010560001000800020006D400020008000100012Q0018012Q00013Q001056000100090002000290010200093Q0010560001000A00020002900102000A3Q0010560001000B00020002900102000B3Q0010560001000C00022Q002A01023Q000E00300D0002000D000E00302Q0002000F001000302Q00020011001200302Q00020013001400302Q00020015001600300D00020017001800302Q00020019001A00302Q0002001B001C00302Q0002001D001E00302Q0002001F00200030050002002100220030050002002300240030050002002500260030050002002700280006D40003000C000100012Q0018012Q00023Q0010560001002900032Q00AA2Q0100024Q0024012Q00013Q000D7Q0003083Q00061A012Q00030001000100049F012Q000300012Q00AA2Q0100023Q00061A0102000600013Q00049F012Q000600012Q00AA010200024Q00AA012Q00024Q0024012Q00019Q002Q0003054Q0066000300016Q0003000300024Q00033Q00034Q000300028Q00017Q00053Q00028Q00026Q00244003043Q006D61746803053Q00666C2Q6F72026Q00E03F02163Q00060B010200030001000100049F012Q00030001001291000200013Q0010910102000200022Q003601033Q0002000E112Q01000D0001000300049F012Q000D0001001220010400033Q0020100104000400040020600005000300052Q00890004000200022Q00CC0004000400022Q00AA010400023Q001220010400033Q0020100104000400042Q0085010500033Q0020600005000500052Q00890004000200022Q0085010400044Q00CC0004000400022Q00AA010400024Q0024012Q00017Q00053Q0003063Q00737472696E6703063Q00666F726D617403023Q00252E028Q0003013Q0066020C3Q001220010200013Q002010010200020002001291000300033Q00060B010400060001000100049F012Q00060001001291000400043Q001291000500054Q006B0103000300052Q001801046Q0056010200044Q003500026Q0024012Q00019Q002Q00050B3Q00066A010200030001000100049F012Q000300012Q00AA010300024Q002Q01053Q00012Q002Q0106000200012Q00CC0005000500062Q00660006000400034Q0005000500064Q0005000300054Q000500028Q00017Q000D4Q00034Q00028Q0003053Q006C6F77657203083Q00746F737472696E6703043Q0066696E64026Q00F03F025Q00408F40026Q0059402Q033Q00737562026Q00184003013Q0020026Q00104002483Q0026963Q00040001000100049F012Q000400010026473Q00060001000200049F012Q00060001001291000200034Q00AA010200023Q00201100023Q00042Q00890002000200022Q0018012Q00023Q001220010200054Q0018010300014Q00890002000200020020110002000200042Q00890002000200022Q00182Q0100023Q0020110002000100062Q001801045Q001291000500074Q0065010600014Q008C0102000600020006930002001F00013Q00049F012Q001F00010010760003000800020026470002001C0001000700049F012Q001C0001001291000400093Q0006FC0004001D0001000100049F012Q001D0001001291000400034Q009E0103000300042Q00AA010300023Q001291000300033Q001291000400074Q001E000500053Q001291000600074Q000100075Q001291000800073Q0004F3000600460001002011000A3Q000A2Q0018010C00094Q0018010D00094Q008C010A000D0002002011000B000100062Q0018010D000A4Q0018010E00044Q0065010F00014Q008C010B000F00020006FC000B00330001000100049F012Q003300012Q001E000C000C4Q00AA010C00023Q0006930005003900013Q00049F012Q00390001002060000C0005000700066A010B00390001000C00049F012Q0039000100206000030003000B002696000B00410001000700049F012Q00410001002011000C0001000A00203E000E000B000700203E000F000B00072Q008C010C000F0002002647000C00420001000C00049F012Q0042000100206000030003000D0020600003000300072Q00180105000B3Q0020600004000B00070004510006002600012Q00AA010300024Q0024012Q00017Q00143Q0003063Q00747970656F6603063Q00436F6C6F723303083Q00746F737472696E6703043Q006773756203013Q0023034Q0003023Q002573026Q0008402Q033Q00737562026Q00F03F2Q033Q00726570027Q0040026Q00184003053Q006D6174636803023Q00255803073Q0066726F6D52474203083Q00746F6E756D626572026Q003040026Q001040026Q001440014F3Q0012202Q0100014Q001801026Q0089000100020002002647000100060001000200049F012Q000600012Q00AA012Q00023Q0012202Q0100034Q002A00028Q00010002000200202Q00010001000400122Q000300053Q00122Q000400066Q00010004000200202Q00010001000400122Q000300073Q00122Q000400066Q0001000400026Q00016Q00015Q00262Q0001002B0001000800049F012Q002B000100201100013Q00090012910003000A3Q0012910004000A4Q008C2Q010004000200201100010001000B0012910003000C4Q008C2Q010003000200201100023Q00090012910004000C3Q0012910005000C4Q008C01020005000200201100020002000B0012160004000C6Q00020004000200202Q00033Q000900122Q000500083Q00122Q000600086Q00030006000200202Q00030003000B00122Q0005000C6Q0003000500026Q000100032Q000100015Q002647000100330001000D00049F012Q0033000100201100013Q000E0012910003000F4Q008C2Q01000300020006930001003500013Q00049F012Q003500012Q001E000100014Q00AA2Q0100023Q0012202Q0100023Q0020102Q0100010010001220010200113Q00201100033Q00090012910005000A3Q0012910006000C4Q008C010300060002001291000400124Q008C010200040002001220010300113Q00201100043Q0009001291000600083Q001291000700134Q008C010400070002001291000500124Q008C010300050002001220010400113Q00201100053Q0009001291000700143Q0012910008000D4Q008C010500080002001291000600124Q0072010400064Q00922Q016Q003500016Q0024012Q00017Q00063Q0003063Q00737472696E6703063Q00666F726D6174030C3Q0025303258253032582530325803013Q005203013Q004703013Q004201113Q0006D400013Q000100012Q00707Q00120D010200013Q00202Q00020002000200122Q000300036Q000400013Q00202Q00053Q00044Q0004000200024Q000500013Q00202Q00063Q00054Q0005000200024Q000600013Q00201001073Q00062Q00F6000600074Q009201026Q003500026Q0024012Q00013Q00013Q00073Q0003043Q006D61746803053Q00666C2Q6F7203053Q00636C616D70028Q00026Q00F03F025Q00E06F40026Q00E03F010D3Q0012202Q0100013Q0020102Q01000100022Q007000025Q0020100102000200032Q001801035Q001291000400043Q001291000500054Q008C01020005000200208A01020002000600202Q0002000200074Q000100026Q00019Q0000017Q00043Q0003043Q007479706503053Q007461626C6503053Q00706169727303083Q00642Q6570436F707901143Q0012202Q0100014Q001801026Q0089000100020002002696000100060001000200049F012Q000600012Q00AA012Q00024Q002A2Q015Q001220010200034Q001801036Q005E00020002000400049F012Q001000012Q007000075Q0020100107000700042Q0018010800064Q00890007000200022Q004A2Q01000500070006770002000B0001000200049F012Q000B00012Q00AA2Q0100024Q0024012Q00017Q00033Q00028Q0003053Q007061697273026Q00F03F010A3Q0012BC000100013Q00122Q000200026Q00038Q00020002000400044Q00060001002060000100010003000677000200050001000100049F012Q000500012Q00AA2Q0100024Q0024012Q00017Q00013Q0003063Q00697061697273020C3Q001220010200014Q001801036Q005E00020002000400049F012Q0007000100066A010600070001000100049F012Q000700012Q00AA010500023Q000677000200040001000200049F012Q000400012Q001E000200024Q00AA010200024Q0024012Q00017Q00043Q0003053Q007061697273026Q00F03F03053Q007461626C6503043Q00736F727401114Q002A2Q015Q001220010200014Q001801036Q005E00020002000400049F012Q000800012Q0001000600013Q0020600006000600022Q004A2Q0100060005000677000200050001000100049F012Q00050001001220010200033Q0020100102000200042Q0018010300013Q00029001046Q004D0102000400012Q00AA2Q0100024Q0024012Q00013Q00013Q00013Q0003083Q00746F737472696E67020C3Q0012B0000200016Q00038Q00020002000200122Q000300016Q000400016Q00030002000200062Q000200090001000300049F012Q000900012Q001200026Q0065010200014Q00AA010200024Q0024012Q00017Q00054Q0003043Q006E6F6E6503043Q004E616D6503083Q00746F737472696E6703053Q00752Q70657201123Q0026473Q00040001000100049F012Q00040001001291000100024Q00AA2Q0100023Q0020102Q013Q00030006FC0001000A0001000100049F012Q000A00010012202Q0100044Q001801026Q00890001000200022Q007000026Q00160102000200010006FC000200100001000100049F012Q001000010020110002000100052Q00890002000200022Q00AA010200024Q0024012Q00017Q002A3Q00030A3Q00636F72652F5468656D6503073Q002Q5F696E64657803053Q00546F6B656E03073Q006973546F6B656E03053Q004672616D65030F3Q00426F7264657253697A65506978656C028Q0003163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F030D3Q004175746F6D6174696353697A6503043Q004E6F6E65030E3Q005363726F2Q6C696E674672616D65031A3Q005363726F2Q6C426172496D6167655472616E73706172656E637903123Q005363726F2Q6C426172546869636B6E652Q73026Q000840030A3Q0043616E76617353697A6500030F3Q00456C61737469634265686176696F7203053Q004E6576657203123Q005363726F2Q6C696E67446972656374696F6E03013Q005903093Q00546578744C6162656C03083Q0052696368546578740100030E3Q005465787458416C69676E6D656E7403043Q004C656674030E3Q005465787459416C69676E6D656E7403063Q0043656E746572030A3Q005465787442752Q746F6E030F3Q004175746F42752Q746F6E436F6C6F7203043Q0054657874034Q0003073Q0054657874426F7803103Q00436C656172546578744F6E466F637573030A3Q00496D6167654C6162656C030B3Q00496D61676542752Q746F6E03083Q00466F6E74466163652Q033Q004E657703063Q00436F726E657203063Q005374726F6B6503073Q0050612Q64696E6703043Q004C697374015C4Q00182Q015Q001291000200014Q00890001000200022Q002A01026Q002A01035Q0010560003000200030006D400043Q000100012Q0018012Q00033Q0010560002000300040006D400040001000100012Q0018012Q00033Q0010560002000400042Q002A01053Q00072Q002A01063Q00030030050006000600070030050006000800090030050006000A000B0010560005000500062Q002A01063Q000700300D00060006000700302Q00060008000900302Q0006000D000900302Q0006000E000F00302Q0006001000110030050006001200130030050006001400150010560005000C00062Q002A01063Q000500300D00060006000700302Q00060008000900302Q00060017001800302Q00060019001A00302Q0006001B001C0010560005001600062Q002A01063Q000600300D00060006000700302Q00060008000900302Q0006001E001800302Q0006001F002000302Q00060019001A0030050006001B001C0010560005001D00062Q002A01063Q000500300D00060006000700302Q00060008000900302Q00060022001800302Q00060019001A00302Q0006001B001C0010560005002100062Q002A01063Q00020030050006000600070030050006000800090010560005002300062Q002A01063Q00030030050006000600070030050006000800090030050006001E00180010560005002400062Q002A01063Q000600300D0006000A000A00302Q00060012001200302Q00060014001400302Q00060019001900302Q0006001B001B0030050006002500110006D400070002000100012Q0018012Q00063Q0006D400080003000100042Q0018012Q00054Q0018012Q00074Q0018012Q00044Q0018012Q00013Q0010560002002600080006D400080004000100022Q0018012Q00024Q0018012Q00013Q0010560002002700080006D400080005000100012Q0018012Q00023Q0010560002002800080006D400080006000100012Q0018012Q00023Q0010560002002900080006D400080007000100012Q0018012Q00023Q0010560002002A00080006D400080008000100022Q0018012Q00014Q0018012Q00023Q0010560002001F00082Q00AA010200024Q0024012Q00013Q00093Q00023Q00030C3Q007365746D6574617461626C6503043Q007061746801073Q001267000100016Q00023Q000100102Q000200026Q00038Q000100036Q00019Q0000017Q00033Q0003043Q007479706503053Q007461626C65030C3Q006765746D6574617461626C65010F3Q0012202Q0100014Q001801026Q00890001000200020026470001000B0001000200049F012Q000B00010012202Q0100034Q001801026Q00890001000200022Q007000025Q0006402Q01000C0001000200049F012Q000C00012Q001200016Q00652Q0100014Q00AA2Q0100024Q0024012Q00017Q00043Q0003043Q007479706503063Q00737472696E6703043Q00456E756D03053Q007063612Q6C021C3Q001220010200014Q0018010300014Q00890002000200020026470002001A0001000200049F012Q001A00012Q007000026Q0016010200023Q0006930002001A00013Q00049F012Q001A0001001220010200034Q007000036Q0016010300034Q00160102000200030006930002001900013Q00049F012Q00190001001220010300043Q0006D400043Q000100022Q0018012Q00024Q0018012Q00014Q005E0003000200040006930003001900013Q00049F012Q001900010006930004001900013Q00049F012Q001900012Q00AA010400024Q00A801026Q00AA2Q0100024Q0024012Q00013Q00018Q00054Q00708Q0070000100014Q0016014Q00012Q00AA012Q00024Q0024012Q00017Q00093Q0003083Q00496E7374616E63652Q033Q006E657703053Q0070616972730003053Q007063612Q6C03063Q00506172656E7403043Q0042696E6403043Q007061746803063Q0069706169727303463Q001220010300013Q0020100103000300022Q001801046Q00890003000200022Q007000046Q0016010400043Q0006930004001800013Q00049F012Q00180001001220010500034Q0018010600044Q005E00050002000700049F012Q00160001002696000900150001000400049F012Q00150001001220010A00053Q0006D4000B3Q000100042Q0018012Q00034Q0018012Q00084Q00703Q00014Q0018012Q00094Q0004010A000200012Q00A801085Q0006770005000C0001000200049F012Q000C00012Q001E000500053Q0006930001003600013Q00049F012Q00360001001220010600034Q0018010700014Q005E00060002000800049F012Q00340001002647000900230001000600049F012Q002300012Q00180105000A3Q00049F012Q003400012Q0070000B00024Q0018010C000A4Q0089000B00020002000693000B002F00013Q00049F012Q002F00012Q0070000B00033Q002010010B000B00072Q0018010C00034Q0018010D00093Q002010010E000A00082Q004D010B000E000100049F012Q003400012Q0070000B00014Q0018010C00094Q0018010D000A4Q008C010B000D00022Q004A01030009000B0006770006001F0001000200049F012Q001F00010006930002004100013Q00049F012Q00410001001220010600094Q0018010700024Q005E00060002000800049F012Q003F0001000693000A003F00013Q00049F012Q003F0001001056000A000600030006770006003C0001000200049F012Q003C00010006930005004400013Q00049F012Q004400010010560003000600052Q00AA010300024Q0024012Q00013Q00018Q00084Q00708Q0070000100014Q0070000200024Q0070000300014Q0070000400034Q008C0102000400022Q004A012Q000100022Q0024012Q00017Q00093Q002Q033Q004E657703083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D2Q033Q006E6577028Q002Q033Q00476574030A3Q007261646975732E63746C03063Q00506172656E7402134Q009701025Q00202Q00020002000100122Q000300026Q00043Q000200122Q000500043Q00202Q00050005000500122Q000600063Q00062Q0007000D00013Q00049F012Q000D00012Q0070000700013Q002010010700070007001291000800084Q00890007000200022Q008C0105000700020010A101040003000500102Q0004000900014Q000200046Q00029Q0000017Q000D3Q002Q033Q004E657703083Q0055495374726F6B6503053Q00436F6C6F7203053Q00546F6B656E030B3Q00636F6C6F722E7768697465030C3Q005472616E73706172656E6379030A3Q00616C7068612E6C696E6503093Q00546869636B6E652Q73026Q00F03F030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203063Q00506172656E74031B4Q006C01035Q00202Q00030003000100122Q000400026Q00053Q00054Q00065Q00202Q00060006000400062Q000700090001000100049F012Q00090001001291000700054Q00890006000200020010560005000300062Q007000065Q00201001060006000400060B010700100001000200049F012Q00100001001291000700074Q00890006000200020010560005000600060030050005000800090012200106000B3Q00201001060006000A00201001060006000C0010A10105000A000600102Q0005000D6Q000300056Q00039Q0000017Q000A3Q00028Q002Q033Q004E657703093Q00554950612Q64696E67030A3Q0050612Q64696E67546F7003043Q005544696D2Q033Q006E6577030C3Q0050612Q64696E675269676874030D3Q0050612Q64696E67426F2Q746F6D030B3Q0050612Q64696E674C65667403063Q00506172656E74052C3Q0006FC000100030001000100049F012Q00030001001291000100013Q0006FC000200060001000100049F012Q000600012Q0018010200013Q0006FC000300090001000100049F012Q000900012Q0018010300013Q0006FC0004000C0001000100049F012Q000C00012Q0018010400024Q007000055Q002010010500050002001291000600034Q002A01073Q0005001220010800053Q002010010800080006001291000900014Q0018010A00014Q008C0108000A0002001056000700040008001220010800053Q002010010800080006001291000900014Q0018010A00024Q008C0108000A0002001056000700070008001220010800053Q002010010800080006001291000900014Q0018010A00034Q008C0108000A0002001056000700080008001220010800053Q0020B001080008000600122Q000900016Q000A00046Q0008000A000200102Q00070009000800102Q0007000A6Q000500076Q00059Q0000017Q000C3Q002Q033Q004E6577030C3Q0055494C6973744C61796F757403073Q0050612Q64696E6703043Q005544696D2Q033Q006E6577028Q00030D3Q0046692Q6C446972656374696F6E03043Q00456E756D03083Q00566572746963616C03093Q00536F72744F72646572030B3Q004C61796F75744F7264657203063Q00506172656E74031A4Q009701035Q00202Q00030003000100122Q000400026Q00053Q000400122Q000600043Q00202Q00060006000500122Q000700063Q00062Q0008000A0001000100049F012Q000A0001001291000800064Q008C01060008000200105600050003000600060B010600110001000200049F012Q00110001001220010600083Q002010010600060007002010010600060009001056000500070006001220010600083Q00201001060006000A00201001060006000B0010A10105000A000600102Q0005000C6Q000300056Q00039Q0000017Q00133Q0003023Q00756903043Q006D6F6E6F03093Q00746578742E6D6F6E6F2Q033Q0074616203083Q00746578742E74616203053Q00736D612Q6C030A3Q00746578742E736D612Q6C03073Q00746578742E756903053Q007469746C6503083Q00466F6E744661636503043Q00466F6E7403083Q005465787453697A652Q033Q00476574030A3Q0054657874436F6C6F72330003053Q00546F6B656E03093Q00636F6C6F722E6D69642Q033Q004E657703093Q00546578744C6162656C03403Q0006FC000100030001000100049F012Q00030001001291000100013Q002647000100080001000200049F012Q00080001001291000300033Q0006FC000300130001000100049F012Q001300010026470001000D0001000400049F012Q000D0001001291000300053Q0006FC000300130001000100049F012Q00130001002647000100120001000600049F012Q00120001001291000300073Q0006FC000300130001000100049F012Q00130001001291000300083Q002696000100170001000400049F012Q001700010026470001001A0001000900049F012Q001A0001001291000400013Q0006FC0004001B0001000100049F012Q001B00012Q0018010400013Q0006FC3Q001F0001000100049F012Q001F00012Q002A01056Q0018012Q00053Q00201001053Q000A0006FC000500260001000100049F012Q002600012Q007000055Q00201001050005000B2Q0018010600044Q00890005000200020010563Q000A000500201001053Q000C0006FC0005002E0001000100049F012Q002E00012Q007000055Q00201001050005000D2Q0018010600034Q00890005000200020010563Q000C000500201001053Q000E002647000500370001000F00049F012Q003700012Q0070000500013Q002010010500050010001291000600114Q00890005000200020010563Q000E00052Q0070000500013Q00201001050005001200060B0106003C0001000200049F012Q003C0001001291000600134Q001801076Q0056010500074Q003500056Q0024012Q00017Q00213Q0003093Q00636F72652F5574696C030B3Q00636F72652F5369676E616C03063Q00546F6B656E7303073Q004368616E6765642Q033Q006E657703023Q007569032A3Q00726278612Q7365743A2Q2F666F6E74732F66616D696C6965732F4275696C64657253616E732E6A736F6E03293Q00726278612Q7365743A2Q2F666F6E74732F66616D696C6965732F4D6F6E7473652Q7261742E6A736F6E03043Q006D6F6E6F03293Q00726278612Q7365743A2Q2F666F6E74732F66616D696C6965732F526F626F746F4D6F6E6F2E6A736F6E032C3Q00726278612Q7365743A2Q2F666F6E74732F66616D696C6965732F536F7572636553616E7350726F2E6A736F6E03063Q0066616D696C7903063Q0077656967687403063Q004D656469756D03063Q007374726F6E6703083Q0053656D69426F6C6403053Q00736D612Q6C03073Q00526567756C617203043Q00466F6E74030D3Q00536574466F6E7446616D696C792Q033Q00476574030C3Q007365746D6574617461626C6503063Q002Q5F6D6F646503013Q006B03043Q0042696E6403063Q00556E62696E6403073Q0052657374796C6503083Q00536574546F6B656E03093Q00536574412Q63656E7403093Q00476574412Q63656E7403053Q00412Q706C7903053Q005265736574030C3Q0042696E64696E67436F756E7401614Q00182Q015Q001291000200014Q00890001000200022Q001801025Q001291000300024Q00890002000200022Q002A01035Q0006D400043Q000100012Q0018012Q00013Q0006D400050001000100012Q0018012Q00044Q0018010600054Q00F20006000100020010560003000300060020100106000200052Q00F20006000100020010560003000400062Q002A01063Q00022Q002A010700023Q001291000800073Q001291000900084Q00250007000200010010560006000600072Q002A010700023Q0012910008000A3Q0012910009000B4Q00250007000200010010560006000900072Q005A00073Q00044Q00083Q000200302Q0008000C000600302Q0008000D000E00102Q0007000600084Q00083Q000200302Q0008000C000600302Q0008000D001000102Q0007000F00084Q00083Q000200302Q0008000C000600302Q0008000D000E00102Q0007001100084Q00083Q000200302Q0008000C000900302Q0008000D001200102Q0007000900084Q00085Q0006D400090002000100032Q0018012Q00084Q0018012Q00074Q0018012Q00063Q0010560003001300090006D400090003000100022Q0018012Q00064Q0018012Q00083Q0010560003001400090006D400090004000100012Q0018012Q00033Q0010CB00030015000900122Q000900166Q000A8Q000B3Q000100302Q000B001700184Q0009000B00020006D4000A0005000100022Q0018012Q00094Q0018012Q00033Q00105600030019000A0006D4000A0006000100012Q0018012Q00093Q0010560003001A000A0006D4000A0007000100022Q0018012Q00094Q0018012Q00033Q0010560003001B000A0006D4000A0008000100012Q0018012Q00033Q0010560003001C000A0006D4000A0009000100022Q0018012Q00014Q0018012Q00033Q0010560003001D000A0006D4000A000A000100012Q0018012Q00033Q0010560003001E000A0006D4000A000B000100012Q0018012Q00033Q0010560003001F000A0006D4000A000C000100032Q0018012Q00034Q0018012Q00054Q0018012Q00083Q00105600030020000A0006D4000A000D000100012Q0018012Q00093Q00105600030021000A2Q00AA010300024Q0024012Q00013Q000E3Q00013Q00030A3Q00686578546F436F6C6F7201064Q00DD00015Q00202Q0001000100014Q00028Q000100026Q00019Q0000017Q00573Q0003053Q00636F6C6F722Q033Q0077696E03063Q00436F6C6F723303073Q0066726F6D524742026Q003840026Q003B4003043Q006D61736B026Q003940026Q003C4003083Q00656C657661746564026Q002Q4003063Q00612Q63656E7403063Q0045464346443903093Q00612Q63656E7444696D03063Q0044352Q41423903083Q00612Q63656E744F6E03063Q0031373133313503023Q00686903063Q004436443644412Q033Q006D696403063Q0039353935394203023Q006C6F03063Q0035453545363503063Q0064616E67657203063Q0045303730374103043Q007761726E03063Q0044394145364103053Q0077686974652Q033Q006E6577026Q00F03F03053Q00626C61636B028Q0003053Q00616C706861027B14AE47E17AB43F03053Q0070616E656C025A643BDF4F8DEF3F03043Q0077652Q6C023D0AD7A3703DEE3F03093Q0077652Q6C486F7665720248E17A14AE47ED3F03043Q006C696E6503083Q006C696E65536F66740214AE47E17A14EE3F03083Q00726F77486F766572020AD7A3703D0AEF3F03053Q00706F707570027B14AE47E17AA43F03053Q00736372696D029A5Q99E13F03083Q0064697361626C656402CD5QCCE43F03063Q00726164697573026Q0022402Q033Q00626F78026Q0014402Q033Q0063746C026Q00104003043Q0070692Q6C025Q00388F4003043Q0073697A652Q033Q00726F77026Q00334003043Q0074616273026Q00414003043Q00662Q6F74026Q00364003083Q00636865636B626F7803063Q007374726F6B6503093Q007363726F2Q6C626172026Q00084003063Q00736C69646572025Q00805340030B3Q00736C69646572547261636B03063Q00737761746368026Q0026402Q033Q007061642Q033Q0067617003083Q00706F7075704D6178025Q00C0624003043Q007465787403023Q0075692Q033Q00746162026Q00284003043Q006D6F6E6F026Q00244003053Q007469746C6503053Q00736D612Q6C006F4Q00BE5Q00054Q00013Q000D00122Q000200033Q00202Q00020002000400122Q000300053Q00122Q000400053Q00122Q000500066Q00020005000200102Q00010002000200122Q000200033Q00202Q00020002000400122Q000300083Q00122Q000400083Q00122Q000500096Q00020005000200102Q00010007000200122Q000200033Q00202Q00020002000400122Q000300093Q00122Q000400093Q00122Q0005000B6Q00020005000200102Q0001000A00024Q00025Q00122Q0003000D6Q00020002000200102Q0001000C00024Q00025Q00122Q0003000F6Q00020002000200102Q0001000E00024Q00025Q00122Q000300116Q00020002000200102Q0001001000024Q00025Q00122Q000300136Q00020002000200102Q0001001200024Q00025Q00122Q000300156Q00020002000200102Q0001001400024Q00025Q00122Q000300176Q00020002000200102Q0001001600024Q00025Q00122Q000300196Q00020002000200102Q0001001800024Q00025Q00122Q0003001B6Q00020002000200102Q0001001A000200122Q000200033Q00202Q00020002001D00122Q0003001E3Q00122Q0004001E3Q00122Q0005001E6Q00020005000200102Q0001001C000200122Q000200033Q00202Q00020002001D00122Q000300203Q00122Q000400203Q00122Q000500206Q00020005000200102Q0001001F000200104Q000100014Q00013Q000A00302Q00010002002200302Q00010023002400302Q00010025002600302Q00010027002800302Q00010029002800302Q0001002A002B00302Q0001002C002D00302Q0001002E002F00302Q0001003000310030050001003200330010563Q002100012Q002A2Q013Q000400308600010002003500302Q00010036003700302Q00010038003900302Q0001003A003B00104Q003400014Q00013Q000C00302Q0001003D003E00302Q0001003F004000302Q00010041004200302Q00010043003500300D00010044001E00302Q00010045004600302Q00010047004800302Q00010049004600302Q0001004A004B0030050001004C00350030050001004D00350030050001004E004F0010563Q003C00012Q00A02Q013Q000500302Q00010051004B00302Q00010052005300302Q00010054005500302Q00010056004B00302Q00010057005500104Q005000016Q00028Q00017Q000D3Q0003023Q00756903043Q00456E756D030A3Q00466F6E7457656967687403063Q0077656967687403063Q0069706169727303063Q0066616D696C7903053Q007063612Q6C03043Q00466F6E742Q033Q006E657703093Q00466F6E745374796C6503063Q004E6F726D616C03083Q0066726F6D456E756D030A3Q00536F7572636553616E73013E3Q0006FC3Q00030001000100049F012Q000300010012913Q00014Q007000016Q00162Q0100013Q0006930001000A00013Q00049F012Q000A00012Q007000016Q00162Q0100014Q00AA2Q0100024Q0070000100014Q00162Q0100013Q0006FC000100100001000100049F012Q001000012Q0070000100013Q0020102Q0100010001001220010200023Q0020100102000200030020100103000100042Q0016010200020003001220010300054Q0070000400023Q0020100105000100062Q00160104000400052Q005E00030002000500049F012Q002A0001001220010800073Q00129A000900083Q00202Q0009000900094Q000A00076Q000B00023Q00122Q000C00023Q00202Q000C000C000A00202Q000C000C000B4Q0008000C000900062Q0008002A00013Q00049F012Q002A00010006930009002A00013Q00049F012Q002A00012Q0070000A6Q004A010A3Q00092Q00AA010900023Q0006770003001A0001000200049F012Q001A0001001220010300073Q001220010400083Q00201001040004000C001220010500023Q00201001050005000800201001050005000D2Q00270003000500040006930003003700013Q00049F012Q003700010006FC0004003A0001000100049F012Q003A0001001220010500023Q00201001050005000800201001040005000D2Q007000056Q004A01053Q00042Q00AA010400024Q0024012Q00017Q00023Q0003023Q00756903293Q00726278612Q7365743A2Q2F666F6E74732F66616D696C6965732F4D6F6E7473652Q7261742E6A736F6E01094Q00272Q018Q000200026Q00035Q00122Q000400026Q0002000200010010560001000100022Q002A2Q016Q00952Q0100014Q0024012Q00017Q00063Q0003063Q00546F6B656E7303083Q00746F737472696E6703063Q00676D6174636803063Q005B5E252E5D2B03043Q007479706503053Q007461626C6501154Q007000015Q0020102Q0100010001001220010200024Q001801036Q0089000200020002002011000200020003001291000400044Q002700020004000400049F012Q00110001001220010600054Q0018010700014Q0089000600020002002696000600100001000600049F012Q001000012Q001E000600064Q00AA010600024Q00162Q0100010005000677000200090001000100049F012Q000900012Q00AA2Q0100024Q0024012Q00017Q00033Q002Q033Q004765740003053Q007063612Q6C03174Q007000036Q0016010300033Q0006FC000300080001000100049F012Q000800012Q002A01046Q0018010300044Q007000046Q004A01043Q00032Q004A0103000100022Q0070000400013Q0020100104000400012Q0018010500024Q0089000400020002002696000400150001000200049F012Q00150001001220010500033Q0006D400063Q000100032Q0018017Q0018012Q00014Q0018012Q00044Q00040105000200012Q00AA012Q00024Q0024012Q00013Q00018Q00054Q00708Q0070000100014Q0070000200024Q004A012Q000100022Q0024012Q00017Q00014Q0001034Q007000015Q0020F900013Q00012Q0024012Q00017Q00063Q0003053Q0070616972732Q033Q004765740003053Q007063612Q6C03073Q004368616E67656403043Q004669726500243Q001220012Q00014Q007000016Q005E3Q0002000200049F012Q00190001001220010500014Q0018010600044Q005E00050002000700049F012Q001600012Q0070000A00013Q002010010A000A00022Q0018010B00094Q0089000A00020002002696000A00140001000300049F012Q00140001001220010B00043Q0006D4000C3Q000100032Q0018012Q00034Q0018012Q00084Q0018012Q000A4Q0004010B000200012Q00A8010A6Q00A801085Q000677000500080001000200049F012Q000800012Q00A801035Q0006773Q00040001000200049F012Q000400012Q00703Q00013Q002010014Q00050006933Q002300013Q00049F012Q002300012Q00703Q00013Q002010014Q00050020115Q00062Q0004012Q000200012Q0024012Q00013Q00018Q00054Q00708Q0070000100014Q0070000200024Q004A012Q000100022Q0024012Q00017Q000B3Q0003083Q00746F737472696E6703063Q00676D6174636803063Q005B5E252E5D2B026Q00F03F03063Q00546F6B656E7303043Q007479706503053Q007461626C6503053Q00652Q726F7203233Q005468656D652E536574546F6B656E3A206E6F207375636820746F6B656E207061746820027Q004003073Q0052657374796C65022B4Q006401025Q00122Q000300016Q00048Q00030002000200202Q00030003000200122Q000500036Q00030005000500044Q000B00012Q0001000700023Q0020600007000700042Q004A010200070006000677000300080001000100049F012Q000800012Q007000035Q00202800030003000500122Q000400046Q000500023Q00202Q00050005000400122Q000600043Q00042Q0004002400012Q00160108000200072Q003200030003000800122Q000800066Q000900036Q00080002000200262Q000800230001000700049F012Q00230001001220010800083Q0012D1000900093Q00122Q000A00016Q000B8Q000A000200024Q00090009000A00122Q000A000A6Q0008000A00010004510004001400012Q0001000400024Q00160104000200042Q004A0103000400012Q007000045Q00201001040004000B2Q005E0104000100012Q0024012Q00017Q00193Q0003043Q007479706503063Q00737472696E67030A3Q00686578546F436F6C6F7203063Q00546F6B656E7303053Q00636F6C6F7203063Q00612Q63656E7403093Q00612Q63656E7444696D03063Q00436F6C6F72332Q033Q006E657703013Q00520285EB51B81E85EB3F03013Q004703013Q004202BC96900F7A36CB3F02A52C431CEBE2E63F025D6DC5FEB27BB23F03083Q00612Q63656E744F6E029A5Q99E13F03073Q0066726F6D524742026Q003740026Q003340026Q003540025Q00406F40025Q00806F4003073Q0052657374796C6501383Q0012202Q0100014Q001801026Q00890001000200020026470001000A0001000200049F012Q000A00012Q007000015Q0020102Q01000100032Q001801026Q00890001000200022Q0018012Q00013Q0006FC3Q000D0001000100049F012Q000D00012Q0024012Q00014Q0070000100013Q00207500010001000400202Q00010001000500102Q000100063Q00122Q000200083Q00202Q00020002000900202Q00033Q000A00202Q00030003000B00202Q00043Q000C00202Q00040004000B00202Q00053Q000D00202Q00050005000B4Q00020005000200102Q00010007000200202Q00023Q000A00102Q0002000E000200202Q00033Q000C00102Q0003000F00034Q00020002000300202Q00033Q000D00102Q0003001000034Q000200020003000E2Q0012002D0001000200049F012Q002D0001001220010300083Q00204300030003001300122Q000400143Q00122Q000500153Q00122Q000600166Q0003000600020006FC000300330001000100049F012Q00330001001220010300083Q00204300030003001300122Q000400173Q00122Q000500173Q00122Q000600186Q0003000600020010560001001100032Q0070000300013Q0020100103000300192Q005E0103000100012Q0024012Q00017Q00033Q0003063Q00546F6B656E7303053Q00636F6C6F7203063Q00612Q63656E7400064Q00707Q002010014Q0001002010014Q0002002010014Q00032Q00AA012Q00024Q0024012Q00017Q00023Q0003063Q00546F6B656E7303073Q0052657374796C65010B3Q0006D400013Q000100012Q0018012Q00014Q0018010200014Q007000035Q0020100103000300012Q001801046Q004D0102000400012Q007000025Q0020100102000200022Q005E0102000100012Q0024012Q00013Q00013Q00053Q0003053Q00706169727303043Q007479706503053Q007461626C6503013Q005200021A3Q001220010200014Q0018010300014Q005E00020002000400049F012Q00170001001220010700024Q0018010800064Q0089000700020002002647000700160001000300049F012Q00160001001220010700024Q001601083Q00052Q0089000700020002002647000700160001000300049F012Q00160001002010010700060004002647000700160001000500049F012Q001600012Q007000076Q001601083Q00052Q0018010900064Q004D01070009000100049F012Q001700012Q004A012Q00050006000677000200040001000200049F012Q000400012Q0024012Q00017Q00023Q0003063Q00546F6B656E7303073Q0052657374796C65000A4Q00708Q0070000100014Q00F20001000100020010563Q000100012Q002A017Q0095012Q00024Q00707Q002010014Q00022Q005E012Q000100012Q0024012Q00017Q00033Q00028Q0003053Q007061697273026Q00F03F000A3Q0012913Q00013Q0012202Q0100024Q007000026Q005E00010002000300049F012Q000600010020605Q0003000677000100050001000100049F012Q000500012Q00AA012Q00024Q0024012Q00017Q00103Q0003043Q0067616D65030A3Q0047657453657276696365030C3Q0054772Q656E5365727669636503083Q004475726174696F6E029A5Q99B93F03053Q005374796C6503043Q00456E756D030B3Q00456173696E675374796C6503043Q005175616403093Q00446972656374696F6E030F3Q00456173696E67446972656374696F6E2Q033Q004F7574030B3Q005365744475726174696F6E03043Q00496E666F03053Q0054772Q656E2Q033Q0053657401243Q00127C2Q0100013Q00202Q00010001000200122Q000300036Q0001000300024Q00025Q00302Q00020004000500122Q000300073Q00202Q00030003000800202Q00030003000900102Q00020006000300122Q000300073Q00202Q00030003000B00202Q00030003000C00102Q0002000A00034Q000300033Q0006D400043Q000100022Q0018012Q00034Q0018012Q00024Q0018010500044Q005E0105000100010006D400050001000100022Q0018012Q00024Q0018012Q00043Q0010560002000D00050006D400050002000100012Q0018012Q00033Q0010560002000E00050006D400050003000100032Q0018012Q00024Q0018012Q00014Q0018012Q00033Q0010560002000F0005000290010500043Q0010560002001000052Q00AA010200024Q0024012Q00013Q00053Q00053Q0003093Q0054772Q656E496E666F2Q033Q006E657703083Q004475726174696F6E03053Q005374796C6503093Q00446972656374696F6E000B3Q0012573Q00013Q00206Q00024Q000100013Q00202Q0001000100034Q000200013Q00202Q0002000200044Q000300013Q00202Q0003000300056Q000300029Q006Q00017Q00043Q0003083Q004475726174696F6E03043Q006D6174682Q033Q006D6178028Q00010A4Q007000015Q001220010200023Q002010010200020003001291000300044Q001801046Q008C0102000400020010560001000100022Q0070000100014Q005E2Q01000100012Q0024012Q00019Q003Q00034Q00708Q00AA012Q00024Q0024012Q00017Q00053Q0003083Q004475726174696F6E028Q0003053Q00706169727303063Q0043726561746503043Q00506C617902174Q007000025Q0020100102000200010026EC0002000D0001000200049F012Q000D0001001220010200034Q0018010300014Q005E00020002000400049F012Q000900012Q004A012Q00050006000677000200080001000200049F012Q000800012Q001E000200024Q00AA010200024Q0070000200013Q0020110002000200042Q001801046Q0070000500024Q0018010600014Q008C0102000600020020110003000200052Q00040103000200012Q00AA010200024Q0024012Q00017Q00013Q0003053Q00706169727302083Q001220010200014Q0018010300014Q005E00020002000400049F012Q000500012Q004A012Q00050006000677000200040001000200049F012Q000400012Q0024012Q00017Q00083Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D6503073Q0043686576726F6E03053Q0043726F2Q7303053Q00436865636B03053Q004D696E757303063Q005365617263682Q033Q00446F74012C4Q00182Q015Q001291000200014Q00890001000200022Q001801025Q001291000300024Q00890002000200022Q002A01035Q0006D400043Q000100012Q0018012Q00013Q0006D400050001000100012Q0018012Q00013Q000290010600023Q0006D400070003000100032Q0018012Q00054Q0018012Q00044Q0018012Q00063Q0010560003000300070006D400070004000100032Q0018012Q00054Q0018012Q00044Q0018012Q00063Q0010560003000400070006D400070005000100032Q0018012Q00054Q0018012Q00044Q0018012Q00063Q0010560003000500070006D400070006000100032Q0018012Q00054Q0018012Q00044Q0018012Q00063Q0010560003000600070006D400070007000100052Q0018012Q00054Q0018012Q00014Q0018012Q00024Q0018012Q00044Q0018012Q00063Q0010560003000700070006D400070008000100012Q0018012Q00013Q0010560003000800072Q00AA010300024Q0024012Q00013Q00093Q00133Q002Q033Q004E657703053Q004672616D65030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F03083Q00506F736974696F6E03053Q005544696D3203093Q0066726F6D5363616C6503043Q0053697A65030A3Q0066726F6D4F2Q6673657403083Q00526F746174696F6E03103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E03083Q00636F6C6F722E6C6F03163Q004261636B67726F756E645472616E73706172656E6379028Q00030F3Q00426F7264657253697A65506978656C03063Q00506172656E7407244Q007000075Q0020100107000700010012DF000800026Q00093Q000800122Q000A00043Q00202Q000A000A000500122Q000B00063Q00122Q000C00066Q000A000C000200102Q00090003000A00122Q000A00083Q00202Q000A000A00092Q0018010B00034Q0018010C00044Q008C010A000C000200105600090007000A001220010A00083Q002010010A000A000B2Q0018010B00014Q0018010C00024Q008C010A000C00020010560009000A000A0010560009000C00052Q0070000A5Q002010010A000A000E00060B010B001C0001000600049F012Q001C0001001291000B000F4Q0089000A000200020010560009000D000A003005000900100011003005000900120011001056000900134Q0056010700094Q003500076Q0024012Q00017Q000A3Q002Q033Q004E657703053Q004672616D6503043Q004E616D6503053Q00476C79706803043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03063Q00506172656E7402104Q007000025Q002010010200020001001291000300024Q002A01043Q0004003005000400030004001220010500063Q0020100105000500072Q0018010600014Q0018010700014Q008C0105000700020010560004000500050030050004000800090010560004000A4Q0056010200044Q003500026Q0024012Q00017Q00023Q0003083Q00536574436F6C6F72030B3Q00536574526F746174696F6E02083Q0006D400023Q000100012Q0018012Q00013Q0010563Q000100020006D400020001000100012Q0018016Q0010563Q000200022Q00AA012Q00024Q0024012Q00013Q00023Q00023Q0003063Q0069706169727303103Q004261636B67726F756E64436F6C6F723301083Q0012202Q0100014Q007000026Q005E00010002000300049F012Q00050001001056000500023Q000677000100040001000200049F012Q000400012Q0024012Q00017Q00013Q0003083Q00526F746174696F6E01034Q007000015Q001056000100014Q0024012Q00017Q000B3Q00026Q00224003043Q006D6174682Q033Q006D6178026Q00084002D7A3703D0AD7E33F026Q00F03F026Q33D33F02B81E85EB51B8DE3F025Q00804640026Q66E63F025Q008046C003273Q0006FC000100030001000100049F012Q00030001001291000100014Q007000036Q001801046Q0018010500014Q008C010300050002001220010400023Q002010010400040003001291000500043Q00201F0106000100052Q008C010400060002001291000500064Q002A010600014Q0070000700014Q0018010800034Q0018010900044Q0018010A00053Q001291000B00073Q001291000C00083Q001291000D00094Q0018010E00024Q008C0107000E00022Q0070000800014Q0018010900034Q0018010A00044Q0018010B00053Q001291000C000A3Q001291000D00083Q001291000E000B4Q0018010F00024Q00720108000F4Q007A01063Q00012Q0070000700024Q002E000800036Q000900066Q000700096Q00079Q0000017Q00063Q00026Q00224002CD5QCCEC3F026Q00F03F026Q00E03F025Q00804640025Q008046C003223Q0006FC000100030001000100049F012Q00030001001291000100014Q007000036Q00A000048Q000500016Q00030005000200202Q0004000100024Q000500016Q000600016Q000700036Q000800043Q00122Q000900033Q00122Q000A00043Q00122Q000B00043Q00122Q000C00056Q000D00026Q0006000D00024Q000700016Q000800036Q000900043Q00122Q000A00033Q00122Q000B00043Q00122Q000C00043Q00122Q000D00066Q000E00026Q0007000E6Q00053Q00012Q0070000600024Q002E000700036Q000800056Q000600086Q00069Q0000017Q00093Q00026Q00224002E17A14AE47E1DA3F026Q00F03F027B14AE47E17AD43F02D7A3703D0AD7E33F025Q008046C002F6285C8FC2F5E83F02713D0AD7A370DD3F025Q0080464003213Q0006FC000100030001000100049F012Q00030001001291000100014Q007000036Q001801046Q0018010500014Q008C0103000500022Q002A010400014Q0070000500014Q0018010600033Q00201F010700010002001291000800033Q001291000900043Q001291000A00053Q001291000B00064Q0018010C00024Q008C0105000C00022Q0070000600014Q0018010700033Q00201F010800010007001291000900033Q001291000A00053Q001291000B00083Q001291000C00094Q0018010D00024Q00720106000D4Q007A01043Q00012Q0070000500024Q002E000600036Q000700046Q000500076Q00059Q0000017Q00053Q00026Q002240029A5Q99E93F026Q00F03F026Q00E03F028Q0003183Q0006FC000100030001000100049F012Q00030001001291000100014Q007000036Q005500048Q000500016Q0003000500024Q00048Q000500016Q000600033Q00202Q00070001000200122Q000800033Q00122Q000900043Q00122Q000A00043Q00122Q000B00056Q000C00026Q0005000C6Q00043Q00012Q0070000500024Q002E000600036Q000700046Q000500076Q00059Q0000017Q001F3Q00026Q00264003043Q006D61746803053Q00666C2Q6F72021F85EB51B81EE53F2Q033Q004E657703053Q004672616D6503083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q66736574028Q0003043Q0053697A6503163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03063Q00506172656E7403063Q00436F726E6572025Q00388F4003083Q0055495374726F6B6503053Q00436F6C6F722Q033Q0047657403043Q006773756203083Q005E636F6C6F72252E03063Q00636F6C6F722E03083Q00636F6C6F722E6C6F03093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657202C3F5285C8FC2D53F02F6285C8FC2F5E83F025Q0080464003083Q00536574436F6C6F7203523Q0006FC000100030001000100049F012Q00030001001291000100014Q007000036Q001801046Q0018010500014Q008C010300050002001220010400023Q00201001040004000300201F0105000100042Q00890004000200022Q0070000500013Q0020100105000500050012DF000600066Q00073Q000400122Q000800083Q00202Q00080008000900122Q0009000A3Q00122Q000A000A6Q0008000A000200102Q00070007000800122Q000800083Q00202Q0008000800092Q0018010900044Q0018010A00044Q008C0108000A00020010560007000B00080030050007000C000D00102B0107000E00034Q0005000700024Q000600013Q00202Q00060006000F00122Q000700106Q000800056Q0006000800014Q000600013Q00202Q00060006000500122Q000700114Q002A01083Q00042Q0070000900023Q0020100109000900130006930002003100013Q00049F012Q00310001002011000A00020014001291000C00153Q001291000D00164Q008C010A000D00020006FC000A00320001000100049F012Q00320001001291000A00174Q008900090002000200105600080012000900300500080018000D0012200109001A3Q00201001090009001900201001090009001B0010560008001900090010560008000E00052Q008C0106000800022Q0070000700034Q0018010800033Q00201F01090001001C001291000A000D3Q001291000B001D3Q001291000C001D3Q001291000D001E4Q0018010E00024Q008C0107000E00022Q002A010800014Q0018010900074Q00250008000100012Q0070000900044Q0018010A00034Q0018010B00084Q008C0109000B0002002010010A0009001F0006D4000B3Q000100022Q0018012Q000A4Q0018012Q00063Q0010560009001F000B2Q00AA010900024Q0024012Q00013Q00013Q00013Q0003053Q00436F6C6F7201064Q002900018Q00028Q0001000200014Q000100013Q00102Q000100018Q00017Q000E3Q00026Q0010402Q033Q004E657703053Q004672616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030C3Q00636F6C6F722E612Q63656E7403163Q004261636B67726F756E645472616E73706172656E6379028Q0003063Q00506172656E7403063Q00436F726E6572025Q00388F40031E3Q0006FC000100030001000100049F012Q00030001001291000100014Q007000035Q00206301030003000200122Q000400036Q00053Q000400122Q000600053Q00202Q0006000600064Q000700016Q000800016Q00060008000200102Q0005000400064Q00065Q00202Q00060006000800062Q000700120001000200049F012Q00120001001291000700094Q00890006000200020010FB00050007000600302Q0005000A000B00102Q0005000C6Q0003000500024Q00045Q00202Q00040004000D00122Q0005000E6Q000600036Q0004000600014Q000300028Q00017Q00143Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C617965727303103Q0055736572496E7075745365727669636503063Q0052657363616E030A3Q0049734578656375746F72030D3Q0048617346696C6573797374656D03083Q0049734D6F62696C65030B3Q004C6F63616C506C6179657203093Q00477569506172656E7403073Q00506C616365496403073Q00482Q747047657403073Q004D616B6544697203063Q0045786973747303043Q005265616403053Q00577269746503063Q0044656C65746503043Q004C69737403063Q005374656D4F6603073Q0053746F72616765015C4Q00A52Q015Q00122Q000200013Q00202Q00020002000200122Q000400036Q00020004000200122Q000300013Q00202Q00030003000200122Q000500046Q0003000500024Q0004000B4Q0065010C5Q0006D4000D3Q000100092Q0018012Q00044Q0018012Q00054Q0018012Q00064Q0018012Q00074Q0018012Q00084Q0018012Q00094Q0018012Q000A4Q0018012Q000B4Q0018012Q000C4Q0018010E000D4Q005E010E000100010006D4000E0001000100012Q0018012Q000D3Q00105600010005000E0006D4000E0002000100022Q0018012Q000C4Q0018012Q000B3Q00105600010006000E0006D4000E0003000100012Q0018012Q000C3Q00105600010007000E0006D4000E0004000100012Q0018012Q00033Q00105600010008000E0006D4000E0005000100012Q0018012Q00023Q00105600010009000E0006D4000E0006000100022Q0018012Q000B4Q0018012Q00023Q0010560001000A000E000290010E00073Q0010560001000B000E000290010E00083Q0010560001000C000E2Q002A010E6Q002A010F6Q002A01105Q000290011100093Q0006D40012000A000100042Q0018012Q000C4Q0018012Q000F4Q0018012Q00074Q0018012Q00083Q0010560010000D00120006D40012000B000100032Q0018012Q000C4Q0018012Q000E4Q0018012Q00063Q0010560010000E00120006D40012000C000100042Q0018012Q000C4Q0018012Q000E4Q0018012Q00104Q0018012Q00053Q0010560010000F00120006D40012000D000100062Q0018012Q000C4Q0018012Q000E4Q0018012Q00114Q0018012Q000F4Q0018012Q00104Q0018012Q00043Q0010560010001000120006D40012000E000100042Q0018012Q000C4Q0018012Q000E4Q0018012Q00104Q0018012Q000A3Q0010560010001100120006D40012000F000100032Q0018012Q000C4Q0018012Q000E4Q0018012Q00093Q001056001000120012000290011200103Q0010560010001300120010560001001400102Q00AA2Q0100024Q0024012Q00013Q00113Q000A3Q0003093Q00777269746566696C6503083Q007265616466696C6503063Q00697366696C6503083Q006973666F6C646572030A3Q006D616B65666F6C64657203093Q006C69737466696C657303073Q0064656C66696C6503063Q0067657468756903043Q007479706503083Q0066756E6374696F6E00233Q001220012Q00014Q0095016Q001220012Q00024Q0095012Q00013Q001220012Q00034Q0095012Q00023Q001220012Q00044Q0095012Q00033Q001220012Q00054Q0095012Q00043Q001220012Q00064Q0095012Q00053Q001220012Q00074Q0095012Q00063Q001220012Q00084Q0095012Q00073Q001220012Q00094Q007000016Q00893Q000200020026473Q001F0001000A00049F012Q001F0001001220012Q00094Q0070000100014Q00893Q000200020026473Q001F0001000A00049F012Q001F0001001220012Q00094Q0070000100024Q00893Q000200020026963Q00200001000A00049F012Q002000012Q00128Q0065012Q00014Q0095012Q00084Q0024012Q00019Q003Q00034Q00708Q005E012Q000100012Q0024012Q00017Q00015Q000A4Q00707Q0006FC3Q00080001000100049F012Q000800012Q00703Q00013Q0026473Q00070001000100049F012Q000700012Q00128Q0065012Q00014Q00AA012Q00024Q0024012Q00019Q003Q00034Q00708Q00AA012Q00024Q0024012Q00017Q00023Q00030C3Q00546F756368456E61626C6564030F3Q004B6579626F617264456E61626C656400094Q00707Q002010014Q00010006933Q000700013Q00049F012Q000700012Q00707Q002010014Q00022Q005F8Q00AA012Q00024Q0024012Q00017Q00013Q00030B3Q004C6F63616C506C6179657200044Q00707Q002010014Q00012Q00AA012Q00024Q0024012Q00017Q00083Q0003053Q007063612Q6C030B3Q004C6F63616C506C61796572030E3Q0046696E6446697273744368696C6403093Q00506C61796572477569030C3Q0057616974466F724368696C6403043Q0067616D65030A3Q004765745365727669636503073Q00436F726547756900284Q00707Q0006933Q000B00013Q00049F012Q000B0001001220012Q00014Q007000016Q005E3Q000200010006933Q000B00013Q00049F012Q000B00010006930001000B00013Q00049F012Q000B00012Q00AA2Q0100023Q001220012Q00013Q0002902Q016Q005E3Q000200010006933Q001300013Q00049F012Q001300010006930001001300013Q00049F012Q001300012Q00AA2Q0100024Q0070000200013Q0020100102000200020006930002002200013Q00049F012Q00220001002011000300020003001291000500044Q008C0103000500020006FC0003001F0001000100049F012Q001F0001002011000300020005001291000500044Q008C0103000500020006930003002200013Q00049F012Q002200012Q00AA010300023Q001220010300063Q00200300030003000700122Q000500086Q000300056Q00039Q0000013Q00013Q00043Q0003043Q0067616D65030A3Q004765745365727669636503073Q00436F726547756903043Q004E616D6500073Q0012E43Q00013Q00206Q000200122Q000200038Q0002000200202Q00013Q00046Q00028Q00017Q00033Q0003053Q007063612Q6C03083Q00746F737472696E6703013Q0030000D3Q001220012Q00013Q0002902Q016Q005E3Q000200010006933Q000A00013Q00049F012Q000A0001001220010200024Q0018010300014Q00890002000200020006FC0002000B0001000100049F012Q000B0001001291000200034Q00AA010200024Q0024012Q00013Q00013Q00023Q0003043Q0067616D6503073Q00506C616365496400043Q001220012Q00013Q002010014Q00022Q00AA012Q00024Q0024012Q00017Q00033Q0003053Q007063612Q6C03043Q007479706503063Q00737472696E67010F3Q0012202Q0100013Q0006D400023Q000100012Q0018017Q005E0001000200020006930001000C00013Q00049F012Q000C0001001220010300024Q0018010400024Q00890003000200020026470003000C0001000300049F012Q000C00012Q00AA010200024Q001E000300034Q00AA010300024Q0024012Q00013Q00013Q00023Q0003043Q0067616D6503073Q00482Q747047657400063Q001220012Q00013Q0020115Q00022Q007000026Q0056012Q00024Q00358Q0024012Q00017Q00023Q0003053Q006D61746368030C3Q005E282E2A292F5B5E2F5D2A2401053Q00200300013Q000100122Q000300026Q000100036Q00019Q0000017Q00053Q002Q0103063Q00676D6174636803053Q005B5E2F5D2B03013Q002F03053Q007063612Q6C01264Q007000015Q0006FC000100070001000100049F012Q000700012Q0070000100013Q0020F900013Q00012Q00652Q0100014Q00AA2Q0100024Q001E000100013Q00201100023Q0002001291000400034Q002700020004000400049F012Q002100010006930001001400013Q00049F012Q001400012Q0018010600013Q001291000700044Q0018010800054Q006B01060006000800060B2Q0100150001000600049F012Q001500012Q00182Q0100053Q001220010600054Q0070000700024Q0018010800014Q00270006000800070006930006001D00013Q00049F012Q001D00010006FC000700210001000100049F012Q00210001001220010800054Q0070000900034Q0018010A00014Q004D0108000A00010006770002000C0001000100049F012Q000C00012Q0065010200014Q00AA010200024Q0024012Q00017Q00034Q0003053Q007063612Q6C3Q01164Q007000015Q0006FC0001000A0001000100049F012Q000A00012Q0070000100014Q00162Q0100013Q002647000100080001000100049F012Q000800012Q001200016Q00652Q0100014Q00AA2Q0100023Q0012202Q0100024Q0070000200024Q001801036Q002700010003000200065D000300140001000100049F012Q00140001002696000200130001000300049F012Q001300012Q001200036Q0065010300014Q00AA010300024Q0024012Q00017Q00023Q0003063Q0045786973747303053Q007063612Q6C01184Q007000015Q0006FC000100060001000100049F012Q000600012Q0070000100014Q00162Q0100014Q00AA2Q0100024Q0070000100023Q0020102Q01000100012Q001801026Q00890001000200020006FC0001000E0001000100049F012Q000E00012Q001E000100014Q00AA2Q0100023Q0012202Q0100024Q0070000200034Q001801036Q00270001000300020006930001001500013Q00049F012Q001500012Q00AA010200024Q001E000300034Q00AA010300024Q0024012Q00017Q00043Q0003083Q00746F737472696E672Q0103073Q004D616B6544697203053Q007063612Q6C02234Q007000025Q0006FC000200110001000100049F012Q001100012Q0070000200013Q001220010300014Q0018010400014Q00890003000200022Q004A01023Q00032Q0070000200024Q001801036Q00890002000200020006930002000F00013Q00049F012Q000F00012Q0070000300033Q0020F90003000200022Q0065010300014Q00AA010300024Q0070000200024Q001801036Q00890002000200020006930002001A00013Q00049F012Q001A00012Q0070000300043Q0020100103000300032Q0018010400024Q0004010300020001001220010300044Q00C4000400056Q00055Q00122Q000600016Q000700016Q000600076Q00033Q00024Q000300028Q00017Q00034Q0003063Q0045786973747303053Q007063612Q6C01154Q007000015Q0006FC000100070001000100049F012Q000700012Q0070000100013Q0020F900013Q00012Q00652Q0100014Q00AA2Q0100024Q0070000100023Q0020102Q01000100022Q001801026Q00890001000200020006FC0001000F0001000100049F012Q000F00012Q00652Q016Q00AA2Q0100023Q0012202Q0100034Q004B000200036Q00038Q0001000300024Q000100028Q00017Q000F3Q002Q033Q00737562026Q00F0BF03013Q002F026Q00F03F027Q00C003053Q00706169727303043Q0066696E6403053Q007461626C6503043Q00736F727403053Q007063612Q6C03043Q007479706503063Q0069706169727303083Q00746F737472696E6703043Q006773756203013Q005C01504Q005B2Q015Q00202Q00023Q000100122Q000400026Q00020004000200262Q0002000B0001000300049F012Q000B000100201100023Q0001001291000400043Q001291000500054Q008C0102000500022Q0018012Q00024Q007000025Q0006FC0002002E0001000100049F012Q002E00012Q001801025Q001291000300034Q006B010200020003001220010300064Q0070000400014Q005E00030002000500049F012Q00270001002011000700060001001291000900044Q0001000A00024Q008C0107000A000200066A010700270001000200049F012Q002700010020110007000600012Q0075010900023Q00202Q0009000900044Q00070009000200202Q00070007000700122Q000900036Q00070009000200062Q000700270001000100049F012Q002700012Q0001000700013Q0020600007000700042Q004A2Q0100070006000677000300150001000100049F012Q00150001001220010300083Q0020100103000300092Q0018010400014Q00040103000200012Q00AA2Q0100023Q0012200102000A4Q0070000300024Q001801046Q00270002000400030006930002003900013Q00049F012Q003900010012200104000B4Q0018010500034Q00890004000200020026960004003A0001000800049F012Q003A00012Q00AA2Q0100023Q0012200104000C4Q0018010500034Q005E00040002000600049F012Q004800012Q0001000900013Q002060000900090004001220010A000D4Q0018010B00084Q0089000A00020002002011000A000A000E001291000C000F3Q001291000D00034Q008C010A000D00022Q004A2Q010009000A0006770004003E0001000200049F012Q003E0001001220010400083Q0020400004000400094Q000500016Q0004000200014Q000100028Q00017Q00053Q0003053Q006D6174636803083Q00285B5E2F5D2B292403043Q006773756203073Q00252E6A736F6E24034Q00010C3Q00201100013Q0001001291000300024Q008C2Q01000300020006FC000100060001000100049F012Q000600012Q00182Q015Q002011000200010003001291000400043Q001291000500054Q008C0102000500022Q00AA010200024Q0024012Q00017Q000E3Q00030B3Q00636F72652F5369676E616C03073Q00546F2Q676C657303073Q004F7074696F6E7303073Q004368616E6765642Q033Q006E657703063Q00746F2Q676C6503063Q006F7074696F6E03083Q005265676973746572030A3Q00556E72656769737465722Q033Q0047657403043Q004669726503043Q004561636803053Q00436F756E7403053Q00436C65617201264Q00182Q015Q001291000200014Q00890001000200022Q002A01026Q002A01035Q0010560002000200032Q002A01035Q0010560002000300030020100103000100052Q00F20003000100020010560002000400032Q002A01033Q00020030050003000600020030050003000700030006D400043Q000100022Q0018012Q00034Q0018012Q00023Q0010560002000800040006D400040001000100012Q0018012Q00023Q0010560002000900040006D400040002000100012Q0018012Q00023Q0010560002000A00040006D400040003000100012Q0018012Q00023Q0010560002000B00040006D400040004000100012Q0018012Q00023Q0010560002000C00040006D400040005000100012Q0018012Q00023Q0010560002000D00040006D400040006000100012Q0018012Q00023Q0010560002000E00042Q00AA010200024Q0024012Q00013Q00073Q000D4Q0003043Q007479706503063Q00737472696E6703053Q00652Q726F7203283Q004175726F72613A20666C6167206E616D6573206D75737420626520737472696E67732C20676F7420026Q000840031A3Q004175726F72613A20756E6B6E6F776E20666C6167206B696E642003083Q00746F737472696E6703073Q00546F2Q676C657303073Q004F7074696F6E7303183Q004175726F72613A206475706C696361746520666C61672022031E3Q0022202Q2D20666C6167206E616D6573206D75737420626520756E6971756503043Q00466C616703333Q002647000100030001000100049F012Q000300012Q00AA010200023Q001220010300024Q0018010400014Q0089000300020002002696000300100001000300049F012Q00100001001220010300043Q0012D1000400053Q00122Q000500026Q000600016Q0005000200024Q00040004000500122Q000500066Q0003000500012Q007000036Q0016010300033Q0006FC0003001C0001000100049F012Q001C0001001220010400043Q0012D1000500073Q00122Q000600086Q00078Q0006000200024Q00050005000600122Q000600066Q0004000600012Q0070000400013Q0020100104000400092Q0016010400040001002647000400260001000100049F012Q002600012Q0070000400013Q00201001040004000A2Q00160104000400010026960004002D0001000100049F012Q002D0001001220010400043Q0012910005000B4Q0018010600013Q0012910007000C4Q006B010500050007001291000600064Q004D0104000600012Q0070000400014Q000F0104000400034Q00040001000200102Q0002000D00014Q000200028Q00017Q00034Q0003073Q00546F2Q676C657303073Q004F7074696F6E73010A3Q0026473Q00030001000100049F012Q000300012Q0024012Q00014Q007000015Q0020802Q010001000200202Q00013Q00014Q00015Q00202Q00010001000300202Q00013Q00016Q00017Q00023Q0003073Q00546F2Q676C657303073Q004F7074696F6E73010A4Q007000015Q0020102Q01000100012Q00162Q0100013Q0006FC000100080001000100049F012Q000800012Q007000015Q0020102Q01000100022Q00162Q0100014Q00AA2Q0100024Q0024012Q00017Q00034Q0003073Q004368616E67656403043Q0046697265020A3Q0026473Q00030001000100049F012Q000300012Q0024012Q00014Q007000025Q0020100102000200020020110002000200032Q001801046Q0018010500014Q004D0102000500012Q0024012Q00017Q00053Q0003053Q00706169727303073Q00546F2Q676C657303063Q00746F2Q676C6503073Q004F7074696F6E7303063Q006F7074696F6E01193Q00120C2Q0100016Q00025Q00202Q0002000200024Q00010002000300044Q000A00012Q001801066Q0018010700044Q0018010800053Q001291000900034Q004D010600090001000677000100050001000200049F012Q000500010012202Q0100014Q007000025Q0020100102000200042Q005E00010002000300049F012Q001600012Q001801066Q0018010700044Q0018010800053Q001291000900054Q004D010600090001000677000100110001000200049F012Q001100012Q0024012Q00017Q00053Q00028Q0003053Q00706169727303073Q00546F2Q676C6573026Q00F03F03073Q004F7074696F6E7300133Q0012913Q00013Q00120C2Q0100026Q00025Q00202Q0002000200034Q00010002000300044Q000700010020605Q0004000677000100060001000100049F012Q000600010012202Q0100024Q007000025Q0020100102000200052Q005E00010002000300049F012Q000F00010020605Q00040006770001000E0001000100049F012Q000E00012Q00AA012Q00024Q0024012Q00017Q00063Q0003053Q00706169727303073Q00546F2Q676C65730003073Q004F7074696F6E7303073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C00193Q00120C012Q00016Q00015Q00202Q0001000100026Q0002000200044Q000800012Q007000045Q0020100104000400020020F90004000300030006773Q00050001000100049F012Q00050001001220012Q00014Q007000015Q0020102Q01000100042Q005E3Q0002000200049F012Q001200012Q007000045Q0020100104000400040020F90004000300030006773Q000F0001000100049F012Q000F00012Q00707Q002010014Q00050020115Q00062Q0004012Q000200012Q0024012Q00017Q00103Q00030B3Q00636F72652F5369676E616C03043Q0067616D65030A3Q004765745365727669636503103Q0055736572496E70757453657276696365028Q0003073Q005072652Q7365642Q033Q006E657703083Q0052656C6561736564030C3Q00497353752Q7072652Q736564030D3Q0053657453752Q7072652Q736564030F3Q00466F726365556E73752Q7072652Q7303043Q0042696E6403053Q00537461727403043Q0053746F7003073Q0043617074757265030B3Q004973436170747572696E67013B4Q00592Q015Q00122Q000200016Q00010002000200122Q000200023Q00202Q00020002000300122Q000400046Q0002000400024Q00038Q00045Q00122Q000500053Q00202Q0006000100074Q00060001000200102Q00030006000600202Q0006000100074Q00060001000200102Q00030008000600029001065Q0006D400070001000100012Q0018012Q00053Q0010560003000900070006D400070002000100012Q0018012Q00053Q0010560003000A00070006D400070003000100012Q0018012Q00053Q0010560003000B00070006D400070004000100012Q0018012Q00043Q0010560003000C00070006D400070005000100042Q0018012Q00064Q0018012Q00034Q0018012Q00054Q0018012Q00044Q001E000800093Q0006D4000A0006000100042Q0018012Q00084Q0018012Q00024Q0018012Q00074Q0018012Q00093Q0010560003000D000A0006D4000A0007000100052Q0018012Q00084Q0018012Q00094Q0018012Q00044Q0018012Q00054Q0018012Q00033Q0010560003000E000A2Q001E000A000A3Q0006D4000B0008000100032Q0018012Q000A4Q0018012Q00024Q0018012Q00063Q0010560003000F000B0006D4000B0009000100012Q0018012Q000A3Q00105600030010000B2Q00AA010300024Q0024012Q00013Q000A3Q00053Q00030D3Q0055736572496E7075745479706503043Q00456E756D03083Q004B6579626F61726403073Q004B6579436F646503043Q004E616D65010D3Q0020C700013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q000100090001000200049F012Q000900010020102Q013Q00040020102Q01000100052Q00AA2Q0100023Q0020102Q013Q00010020102Q01000100052Q00AA2Q0100024Q0024012Q00017Q00013Q00029Q00074Q00707Q000E0F0001000400013Q00049F012Q000400012Q00128Q0065012Q00014Q00AA012Q00024Q0024012Q00017Q00043Q00026Q00F03F03043Q006D6174682Q033Q006D6178028Q00010E3Q0006933Q000600013Q00049F012Q000600012Q007000015Q0020600001000100012Q00952Q015Q00049F012Q000D00010012202Q0100023Q0020102Q0100010003001291000200044Q007000035Q00203E0003000300012Q008C2Q01000300022Q00952Q016Q0024012Q00017Q00013Q00029Q00033Q0012913Q00014Q0095017Q0024012Q00017Q00053Q0003043Q007479706503063Q00737472696E6703043Q004E616D6503053Q007461626C6503063Q00696E7365727402203Q001220010200014Q001801036Q0089000200020002002647000200070001000200049F012Q0007000100060B0102000A00013Q00049F012Q000A000100065D0002000A00013Q00049F012Q000A000100201001023Q00030006FC0002000E0001000100049F012Q000E000100029001036Q00AA010300024Q007000036Q00160103000300020006FC000300160001000100049F012Q001600012Q002A01046Q0018010300044Q007000046Q004A010400020003001220010400043Q0020100104000400052Q0018010500034Q0018010600014Q004D0104000600010006D400040001000100022Q0018012Q00034Q0018012Q00014Q00AA010400024Q0024012Q00013Q00028Q00014Q0024012Q00017Q00033Q0003063Q0069706169727303053Q007461626C6503063Q0072656D6F766500103Q001220012Q00014Q007000016Q005E3Q0002000200049F012Q000D00012Q0070000500013Q00066A0104000D0001000500049F012Q000D0001001220010500023Q0020660105000500034Q00068Q000700036Q00050007000100044Q000F00010006773Q00040001000200049F012Q000400012Q0024012Q00017Q000C3Q0003073Q00556E6B6E6F776E03053Q00626567616E03073Q005072652Q73656403043Q004669726503083Q0052656C6561736564028Q00026Q00F03F026Q00F0BF03053Q007063612Q6C03043Q007761726E031F3Q005B4175726F72615D20686F746B65792068616E646C657220652Q726F723A2003083Q00746F737472696E6703383Q0006930001000300013Q00049F012Q000300012Q0024012Q00014Q007000036Q001801046Q0089000300020002002647000300090001000100049F012Q000900012Q0024012Q00013Q002647000200120001000200049F012Q001200012Q0070000400013Q0020100104000400030020110004000400042Q0018010600034Q001801076Q004D01040007000100049F012Q001800012Q0070000400013Q0020100104000400050020110004000400042Q0018010600034Q001801076Q004D0104000700012Q0070000400023Q000EC80006001C0001000400049F012Q001C00012Q0024012Q00014Q0070000400034Q00160104000400030006FC000400210001000100049F012Q002100012Q0024012Q00014Q0001000500043Q001291000600073Q001291000700083Q0004F30005003700012Q00160109000400080006930009003600013Q00049F012Q00360001001220010A00094Q0018010B00094Q0018010C00024Q0018010D6Q0027000A000D000B0006FC000A00360001000100049F012Q00360001001220010C000A3Q001280000D000B3Q00122Q000E000C6Q000F000B6Q000E000200024Q000D000D000E4Q000C000200010004510005002500012Q0024012Q00017Q00033Q00030A3Q00496E707574426567616E03073Q00436F2Q6E656374030A3Q00496E707574456E64656400134Q00707Q0006933Q000400013Q00049F012Q000400012Q0024012Q00014Q00703Q00013Q002010014Q00010020115Q00020006D400023Q000100012Q00703Q00024Q0048012Q000200029Q006Q00013Q00206Q000300206Q00020006D400020001000100012Q00703Q00024Q008C012Q000200022Q0095012Q00034Q0024012Q00013Q00023Q00013Q0003053Q00626567616E02064Q00AE00028Q00038Q000400013Q00122Q000500016Q0002000500016Q00017Q00013Q0003053Q00656E64656402064Q00AE00028Q00038Q000400013Q00122Q000500016Q0002000500016Q00017Q00053Q00030A3Q00446973636F2Q6E656374028Q0003073Q005072652Q736564030D3Q00446973636F2Q6E656374412Q6C03083Q0052656C6561736564001D4Q00707Q0006933Q000800013Q00049F012Q000800012Q00707Q0020115Q00012Q0004012Q000200012Q001E8Q0095017Q00703Q00013Q0006933Q001000013Q00049F012Q001000012Q00703Q00013Q0020115Q00012Q0004012Q000200012Q001E8Q0095012Q00014Q002A017Q0095012Q00023Q0012913Q00024Q0095012Q00034Q00703Q00043Q002010014Q00030020115Q00042Q0004012Q000200012Q00703Q00043Q002010014Q00050020115Q00042Q0004012Q000200012Q0024012Q00017Q00023Q00030A3Q00496E707574426567616E03073Q00436F2Q6E65637401114Q00B59Q00000100016Q000200013Q00202Q00020002000100202Q0002000200020006D400043Q000100042Q00703Q00024Q0018012Q00014Q00708Q0018017Q008C0102000400022Q00182Q0100023Q0006D400020001000100022Q0018012Q00014Q00708Q00AA010200024Q0024012Q00013Q00023Q00023Q0003073Q00556E6B6E6F776E030A3Q00446973636F2Q6E65637402133Q0006930001000300013Q00049F012Q000300012Q0024012Q00014Q007000026Q001801036Q0089000200020002002647000200090001000100049F012Q000900012Q0024012Q00014Q0070000300013Q00208B0003000300024Q0003000200014Q000300036Q000300026Q000300036Q00048Q000500026Q0003000500016Q00017Q00013Q00030A3Q00446973636F2Q6E65637400094Q00707Q0006933Q000600013Q00049F012Q000600012Q00707Q0020115Q00012Q0004012Q000200012Q001E8Q0095012Q00014Q0024012Q00017Q00015Q00074Q00707Q0026473Q00040001000100049F012Q000400012Q00128Q0065012Q00014Q00AA012Q00024Q0024012Q00017Q00073Q00030B3Q00636F72652F5369676E616C03093Q00636F72652F5574696C03043Q0067616D65030A3Q004765745365727669636503103Q0055736572496E7075745365727669636503063Q00412Q7461636803063Q00526573697A65011D4Q00182Q015Q001291000200014Q00890001000200022Q001801025Q001291000300024Q0089000200020002001220010300033Q002011000300030004001291000500054Q008C0103000500022Q002A01045Q00029001055Q000290010600013Q0006D400070002000100052Q0018012Q00014Q0018012Q00054Q0018012Q00034Q0018012Q00064Q0018012Q00023Q0010560004000600070006D400070003000100052Q0018012Q00014Q0018012Q00054Q0018012Q00034Q0018012Q00064Q0018012Q00023Q0010560004000700072Q00AA010400024Q0024012Q00013Q00043Q00043Q00030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F75636801103Q0020432Q013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000D0001000200049F012Q000D00010020102Q013Q0001001220010200023Q0020100102000200010020100102000200040006402Q01000D0001000200049F012Q000D00012Q001200016Q00652Q0100014Q00AA2Q0100024Q0024012Q00017Q00043Q00030D3Q0055736572496E7075745479706503043Q00456E756D030D3Q004D6F7573654D6F76656D656E7403053Q00546F75636801103Q0020432Q013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000D0001000200049F012Q000D00010020102Q013Q0001001220010200023Q0020100102000200010020100102000200040006402Q01000D0001000200049F012Q000D00012Q001200016Q00652Q0100014Q00AA2Q0100024Q0024012Q00017Q000C3Q0003053Q00636C616D7001002Q033Q006E6577026Q00F03F030A3Q00496E707574426567616E03073Q00436F2Q6E656374030A3Q00496E707574456E646564030C3Q00496E7075744368616E67656403053Q004D6F766564030A3Q0049734472612Q67696E67030A3Q00446973636F2Q6E65637403073Q0044657374726F7903563Q0006FC000100030001000100049F012Q000300012Q00182Q015Q0006FC000200070001000100049F012Q000700012Q002A01036Q0018010200033Q0020100103000200010026470003000B0001000200049F012Q000B00012Q001200036Q0065010300014Q006501046Q001E000500064Q007000075Q0020100107000700032Q00F20007000100022Q002A01085Q0006D400093Q000100012Q0018012Q00044Q0001000A00083Q002060000A000A0004002010010B3Q0005002011000B000B00060006D4000D0001000100052Q00703Q00014Q0018012Q00044Q0018012Q00054Q0018012Q00064Q0018012Q00014Q008C010B000D00022Q004A0108000A000B2Q0001000A00083Q002060000A000A0004002010010B3Q0007002011000B000B00060006D4000D0002000100052Q00703Q00014Q0018012Q00044Q0018012Q00094Q0018012Q00024Q0018012Q00014Q000A010B000D00024Q0008000A000B4Q000A00083Q00202Q000A000A00044Q000B00023Q00202Q000B000B000800202Q000B000B00060006D4000D0003000100082Q0018012Q00044Q00703Q00034Q0018012Q00054Q0018012Q00064Q0018012Q00034Q0018012Q00014Q00703Q00044Q0018012Q00074Q000A010B000D00024Q0008000A000B4Q000A00083Q00202Q000A000A00044Q000B00023Q00202Q000B000B000700202Q000B000B00060006D4000D0004000100052Q00703Q00014Q0018012Q00044Q0018012Q00094Q0018012Q00024Q0018012Q00014Q008C010B000D00022Q004A0108000A000B2Q002A010A3Q0004001056000A000900070006D4000B0005000100012Q0018012Q00043Q001056000A000A000B0006D4000B0006000100022Q0018012Q00084Q0018012Q00073Q001056000A000B000B000290010B00073Q001056000A000C000B2Q00AA010A00024Q0024012Q00013Q00088Q00034Q0065017Q0095017Q0024012Q00017Q00013Q0003083Q00506F736974696F6E010E4Q007000016Q001801026Q00890001000200020006FC000100060001000100049F012Q000600012Q0024012Q00014Q00652Q0100014Q00952Q0100013Q0020102Q013Q00012Q00952Q0100024Q0070000100043Q0020102Q01000100012Q00952Q0100034Q0024012Q00017Q00023Q0003053Q006F6E456E6403083Q00506F736974696F6E01154Q007000016Q001801026Q00890001000200020006FC000100060001000100049F012Q000600012Q0024012Q00014Q0070000100013Q0006930001001400013Q00049F012Q001400012Q0070000100024Q005E2Q01000100012Q0070000100033Q0020102Q01000100010006930001001400013Q00049F012Q001400012Q0070000100033Q0020102Q01000100012Q0070000200043Q0020100102000200022Q00042Q01000200012Q0024012Q00017Q00133Q0003083Q00506F736974696F6E03013Q005803063Q004F2Q6673657403013Q005903093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A65030C3Q004162736F6C75746553697A65030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577028Q0003053Q00636C616D7003043Q006D6174682Q033Q006D6178026Q00F03F03053Q005544696D3203053Q005363616C6503043Q004669726501664Q007000015Q0006930001000800013Q00049F012Q000800012Q0070000100014Q001801026Q00890001000200020006FC000100090001000100049F012Q000900012Q0024012Q00013Q0020102Q013Q00012Q00A1000200026Q0001000100024Q000200033Q00202Q00020002000200202Q00020002000300202Q0003000100024Q0002000200034Q000300033Q00202Q00030003000400202Q00030003000300202Q0004000100044Q0003000300044Q000400043Q00062Q0004005300013Q00049F012Q00530001001220010400053Q0020100104000400060006930004002000013Q00049F012Q00200001001220010400053Q0020100104000400060020100104000400070006930004005300013Q00049F012Q005300012Q0070000500053Q0020100105000500082Q0070000600053Q0020100106000600090006FC0006002D0001000100049F012Q002D00010012200106000A3Q00201001060006000B0012910007000C3Q0012910008000C4Q008C0106000800020020100107000500020020AC0008000600024Q00070007000800202Q00080005000400202Q0009000600044Q0008000800094Q000900063Q00202Q00090009000D4Q000A00026Q000B00073Q00122Q000C000E3Q002010010C000C000F2Q0018010D00073Q002010010E00040002002010010F000500020020100110000600020010760010001000102Q0036010F000F00102Q002Q010E000E000F2Q0072010C000E4Q007301093Q00022Q0018010200094Q0070000900063Q00201001090009000D2Q0018010A00034Q0018010B00083Q001220010C000E3Q002010010C000C000F2Q0018010D00083Q002010010E00040004002010010F000500040020100110000600040010760010001000102Q0036010F000F00102Q002Q010E000E000F2Q0072010C000E4Q007301093Q00022Q0018010300094Q0070000400053Q00124D000500113Q00202Q00050005000B4Q000600033Q00202Q00060006000200202Q0006000600124Q000700026Q000800033Q00202Q00080008000400202Q0008000800124Q000900034Q008C0105000900020010560004000100052Q00AA000400073Q00202Q0004000400134Q000600053Q00202Q0006000600014Q0004000600016Q00017Q00023Q0003053Q006F6E456E6403083Q00506F736974696F6E01144Q007000016Q001801026Q00890001000200020006930001001300013Q00049F012Q001300012Q0070000100013Q0006930001001300013Q00049F012Q001300012Q0070000100024Q005E2Q01000100012Q0070000100033Q0020102Q01000100010006930001001300013Q00049F012Q001300012Q0070000100033Q0020102Q01000100012Q0070000200043Q0020100102000200022Q00042Q01000200012Q0024012Q00019Q003Q00034Q00708Q00AA012Q00024Q0024012Q00017Q00033Q0003063Q00697061697273030A3Q00446973636F2Q6E656374030D3Q00446973636F2Q6E656374412Q6C000E3Q001220012Q00014Q007000016Q005E3Q0002000200049F012Q000600010020110005000400022Q00040105000200010006773Q00040001000200049F012Q000400012Q002A017Q003F9Q003Q00013Q00206Q00036Q000200016Q00017Q00013Q00030A3Q00446973636F2Q6E65637401033Q0020102Q013Q00012Q005E2Q01000100012Q0024012Q00017Q000E3Q0003073Q00566563746F72322Q033Q006E6577026Q006940026Q006440026Q009940025Q00408F40026Q00F03F030A3Q00496E707574426567616E03073Q00436F2Q6E656374030C3Q00496E7075744368616E676564030A3Q00496E707574456E64656403073Q00526573697A6564030A3Q00446973636F2Q6E65637403073Q0044657374726F79054D3Q0006FC000400040001000100049F012Q000400012Q002A01056Q0018010400053Q0006FC0002000C0001000100049F012Q000C0001001220010500013Q00201301050005000200122Q000600033Q00122Q000700046Q0005000700024Q000200053Q0006FC000300140001000100049F012Q00140001001220010500013Q00201301050005000200122Q000600053Q00122Q000700066Q0005000700024Q000300054Q006501056Q001E000600074Q007000085Q0020100108000800022Q00F20008000100022Q002A01096Q0001000A00093Q002060000A000A0007002010010B3Q0008002011000B000B00090006D4000D3Q000100052Q00703Q00014Q0018012Q00054Q0018012Q00064Q0018012Q00074Q0018012Q00014Q000A010B000D00024Q0009000A000B4Q000A00093Q00202Q000A000A00074Q000B00023Q00202Q000B000B000A00202Q000B000B00090006D4000D0001000100092Q0018012Q00054Q00703Q00034Q0018012Q00064Q00703Q00044Q0018012Q00074Q0018012Q00024Q0018012Q00034Q0018012Q00014Q0018012Q00084Q000A010B000D00024Q0009000A000B4Q000A00093Q00202Q000A000A00074Q000B00023Q00202Q000B000B000B00202Q000B000B00090006D4000D0002000100042Q00703Q00014Q0018012Q00054Q0018012Q00044Q0018012Q00014Q008C010B000D00022Q004A0109000A000B2Q002A010A3Q0003001056000A000C00080006D4000B0003000100022Q0018012Q00094Q0018012Q00083Q001056000A000D000B000290010B00043Q001056000A000E000B2Q00AA010A00024Q0024012Q00013Q00053Q00023Q0003083Q00506F736974696F6E030C3Q004162736F6C75746553697A65010E4Q007000016Q001801026Q00890001000200020006FC000100060001000100049F012Q000600012Q0024012Q00014Q00652Q0100014Q00952Q0100013Q0020102Q013Q00012Q00952Q0100024Q0070000100043Q0020102Q01000100022Q00952Q0100034Q0024012Q00017Q000A3Q0003083Q00506F736974696F6E03053Q00636C616D7003013Q005803013Q005903043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403043Q006D61746803053Q00666C2Q6F7203043Q004669726501354Q007000015Q0006930001000800013Q00049F012Q000800012Q0070000100014Q001801026Q00890001000200020006FC000100090001000100049F012Q000900012Q0024012Q00013Q0020102Q013Q00012Q0070000200024Q003Q01000100022Q0070000200033Q0020100102000200022Q0070000300043Q0020100103000300030020100104000100032Q009E0103000300042Q0070000400053Q0020100104000400032Q0070000500063Q0020570105000500034Q0002000500024Q000300033Q00202Q0003000300024Q000400043Q00202Q00040004000400202Q0005000100044Q0004000400054Q000500053Q00202Q0005000500042Q0070000600063Q0020100106000600042Q008C0103000600022Q0070000400073Q001220010500063Q002010010500050007001220010600083Q0020100106000600092Q0018010700024Q0089000600020002001220010700083Q0020100107000700092Q0018010800034Q00F6000700084Q007301053Q00020010560004000500052Q00AA000400083Q00202Q00040004000A4Q000600073Q00202Q0006000600054Q0004000600016Q00017Q00023Q0003053Q006F6E456E6403043Q0053697A6501144Q007000016Q001801026Q00890001000200020006930001001300013Q00049F012Q001300012Q0070000100013Q0006930001001300013Q00049F012Q001300012Q00652Q016Q00952Q0100014Q0070000100023Q0020102Q01000100010006930001001300013Q00049F012Q001300012Q0070000100023Q0020102Q01000100012Q0070000200033Q0020100102000200022Q00042Q01000200012Q0024012Q00017Q00033Q0003063Q00697061697273030A3Q00446973636F2Q6E656374030D3Q00446973636F2Q6E656374412Q6C000E3Q001220012Q00014Q007000016Q005E3Q0002000200049F012Q000600010020110005000400022Q00040105000200010006773Q00040001000200049F012Q000400012Q002A017Q003F9Q003Q00013Q00206Q00036Q000200016Q00017Q00013Q00030A3Q00446973636F2Q6E65637401033Q0020102Q013Q00012Q005E2Q01000100012Q0024012Q00017Q00123Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F5369676E616C03093Q00636F72652F5574696C03043Q0067616D65030A3Q004765745365727669636503103Q0055736572496E7075745365727669636503063Q004163746976650003063Q00436C6F7365642Q033Q006E657703043Q00496E697403043Q00486F737403053Q00436C6F736503083Q00436C6F7365412Q6C03043Q004F70656E03063Q0049734F70656E03073Q0044657374726F79013A4Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q0089000400020002001220010500053Q002011000500050006001291000700074Q008C0105000700022Q002A01065Q00300500060008000900201001070003000B2Q00F20007000100020010560006000A00072Q001E000700083Q0006D400093Q000100022Q0018012Q00074Q0018012Q00013Q0010560006000C00090006D400090001000100012Q0018012Q00073Q0010560006000D0009000290010900023Q0006D4000A0003000100012Q0018012Q00083Q0006D4000B0004000100022Q0018012Q00064Q0018012Q000A3Q0010560006000E000B002010010B0006000E0010560006000F000B0006D4000B0005000100082Q0018012Q00064Q0018012Q00074Q0018012Q00014Q0018012Q00024Q0018012Q00044Q0018012Q00084Q0018012Q00054Q0018012Q00093Q00105600060010000B0006D4000B0006000100012Q0018012Q00063Q00105600060011000B0006D4000B0007000100032Q0018012Q00064Q0018012Q000A4Q0018012Q00073Q00105600060012000B2Q00AA010600024Q0024012Q00013Q00083Q000D3Q0003073Q0044657374726F792Q033Q004E657703053Q004672616D6503043Q004E616D6503053Q004C6179657203043Q0053697A6503053Q005544696D3203093Q0066726F6D5363616C65026Q00F03F03163Q004261636B67726F756E645472616E73706172656E637903063Q005A496E646578025Q00407F4003063Q00506172656E7401194Q007000015Q0006930001000600013Q00049F012Q000600012Q007000015Q0020110001000100012Q00042Q01000200012Q0070000100013Q0020ED00010001000200122Q000200036Q00033Q000500302Q00030004000500122Q000400073Q00202Q00040004000800122Q000500093Q00122Q000600096Q00040006000200102Q0003000600040030050003000A00090030050003000B000C0010560003000D4Q008C2Q01000300022Q00952Q016Q007000016Q00AA2Q0100024Q0024012Q00019Q003Q00034Q00708Q00AA012Q00024Q0024012Q00017Q00043Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q005803013Q0059021A3Q00209200020001000100202Q00030001000200202Q00043Q000300202Q00050002000300062Q000500160001000400049F012Q0016000100201001043Q00030020100105000200030020100106000300032Q009E0105000500060006D7000400160001000500049F012Q0016000100201001043Q00040020100105000200040006D7000500160001000400049F012Q0016000100201001043Q00040020100105000200040020100106000300042Q009E010500050006000677010400020001000500049F012Q001700012Q001200046Q0065010400014Q00AA010400024Q0024012Q00017Q00013Q00030A3Q00446973636F2Q6E65637400094Q00707Q0006933Q000800013Q00049F012Q000800012Q00707Q0020115Q00012Q0004012Q000200012Q001E8Q0095017Q0024012Q00017Q000B3Q0003063Q004163746976650003053Q006672616D6503073Q0044657374726F7903073Q006F6E436C6F736503053Q007063612Q6C03043Q007761726E031E3Q005B4175726F72615D20706F707570206F6E436C6F736520652Q726F723A2003083Q00746F737472696E6703063Q00436C6F73656403043Q004669726500244Q00707Q002010014Q00010006FC3Q00050001000100049F012Q000500012Q0024012Q00014Q007000015Q0030050001000100022Q0070000100014Q005E2Q01000100010020102Q013Q00030006930001000F00013Q00049F012Q000F00010020102Q013Q00030020110001000100042Q00042Q01000200010020102Q013Q00050006930001001E00013Q00049F012Q001E00010012202Q0100063Q00201001023Q00052Q005E0001000200020006FC0001001E0001000100049F012Q001E0001001220010300073Q001280000400083Q00122Q000500096Q000600026Q0005000200024Q0004000400054Q0003000200012Q007000015Q0020102Q010001000A00201100010001000B2Q001801036Q004D2Q01000300012Q0024012Q00017Q00343Q0003053Q00436C6F736503053Q00652Q726F7203333Q004175726F72613A204C617965722E496E6974206D7573742072756E206265666F7265206120706F7075702063616E206F70656E027Q004003053Q007769647468030C3Q004162736F6C75746553697A6503013Q005803043Q0053697A6503013Q005903063Q004F2Q66736574028Q002Q033Q004E657703053Q004672616D6503043Q004E616D6503053Q00506F70757003053Q005544696D32030A3Q0066726F6D4F2Q6673657403103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030E3Q00636F6C6F722E656C65766174656403163Q004261636B67726F756E645472616E73706172656E6379030B3Q00616C7068612E706F70757003103Q00436C69707344657363656E64616E74732Q0103063Q005A496E646578025Q00507F4003063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E626F7803063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503103Q004162736F6C757465506F736974696F6E03053Q00616C69676E03053Q00726967687403053Q00636C616D70026Q00184003043Q006D6174682Q033Q006D6178026Q00104003083Q00506F736974696F6E03053Q00666C2Q6F7203053Q006672616D6503073Q00636F6E74656E7403063Q00616E63686F7203073Q00666C692Q70656403073Q006F6E436C6F736503063Q00526573697A6503063Q00416374697665030A3Q00496E707574426567616E03073Q00436F2Q6E65637403A94Q007000035Q0020100103000300012Q005E0103000100010006FC000200070001000100049F012Q000700012Q002A01036Q0018010200034Q0070000300013Q0006FC0003000E0001000100049F012Q000E0001001220010300023Q001291000400033Q001291000500044Q004D0103000500010020100103000200050006FC000300130001000100049F012Q0013000100201001033Q000600201001030003000700201001040001000800201001040004000900201001040004000A0026EC0004001A0001000B00049F012Q001A00010020100105000100060020100104000500092Q0070000500023Q00201001050005000C0012910006000D4Q002A01073Q00070030050007000E000F001220010800103Q0020100108000800112Q0018010900034Q0018010A00044Q008C0108000A00020010560007000800082Q0070000800023Q00203C00080008001300122Q000900146Q00080002000200102Q0007001200084Q000800023Q00202Q00080008001300122Q000900166Q00080002000200102Q00070015000800302Q00070017001800300500070019001A2Q0070000800013Q0010560007001B00082Q008C0105000700022Q0070000600023Q00201001060006001C2Q0070000700033Q00201001070007001D0012910008001E4Q00890007000200022Q0018010800054Q004D0106000800012Q0070000600023Q00201001060006001F2Q0018010700053Q001291000800203Q001291000900214Q004D0106000900010010560001001B00052Q0070000600013Q0020100106000600222Q0070000700013Q00201001070007000600208D01083Q002200202Q00093Q000600202Q000A0008000700202Q000B000600074Q000A000A000B00202Q000B0002002300262Q000B00550001002400049F012Q00550001002010010B00080007002010010C000900072Q009E010B000B000C002010010C000600072Q002Q010B000B000C2Q002Q010A000B00032Q0070000B00043Q00204A000B000B00254Q000C000A3Q00122Q000D00263Q00122Q000E00273Q00202Q000E000E002800122Q000F00263Q00202Q0010000700074Q00100010000300202Q0010001000264Q000E00106Q000B3Q00024Q000A000B3Q00202Q000B0008000900202Q000C000600094Q000B000B000C00202Q000C000900094Q000B000B000C00202Q000B000B00294Q000C8Q000D000B000400202Q000E0007000900202Q000E000E002600062Q000E00800001000D00049F012Q00800001002010010D00080009002010010E000600092Q002Q010D000D000E2Q002Q010D000D000400203E000D000D0029000E11012600780001000D00049F012Q007800012Q0018010B000D4Q0065010C00013Q00049F012Q00800001001220010E00273Q002010010E000E0028001291000F00263Q0020100110000700092Q002Q01100010000400203E0010001000262Q008C010E001000022Q0018010B000E3Q001220010D00103Q002034000D000D001100122Q000E00273Q00202Q000E000E002B4Q000F000A6Q000E0002000200122Q000F00273Q00202Q000F000F002B4Q0010000B6Q000F00106Q000D3Q000200102Q0005002A000D4Q000D3Q000500102Q000D002C000500102Q000D002D000100102Q000D002E3Q00102Q000D002F000C00202Q000E0002003000102Q000D0030000E0006D4000E3Q000100012Q00707Q001056000D0001000E0006D4000E0001000100022Q0018012Q00054Q0018012Q00033Q001021000D0031000E4Q000E5Q00102Q000E0032000D4Q000E00063Q00202Q000E000E003300202Q000E000E00340006D400100002000100052Q00708Q0018012Q000D4Q00703Q00074Q0018012Q00054Q0018017Q008C010E001000022Q0095010E00054Q00AA010D00024Q0024012Q00013Q00033Q00013Q0003053Q00436C6F736501044Q007000015Q0020102Q01000100012Q005E2Q01000100012Q0024012Q00017Q00033Q0003043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657402084Q007000025Q001220010300023Q0020100103000300032Q0070000400014Q0018010500014Q008C0103000500020010560002000100032Q0024012Q00017Q000B3Q0003063Q0041637469766503073Q004B6579436F646503043Q00456E756D03063Q0045736361706503053Q00436C6F7365030D3Q0055736572496E70757454797065030C3Q004D6F75736542752Q746F6E31030C3Q004D6F75736542752Q746F6E3203053Q00546F75636803083Q00506F736974696F6E03063Q00506172656E7402414Q007000025Q0020100102000200012Q0070000300013Q000640010200060001000300049F012Q000600012Q0024012Q00013Q00201001023Q0002001220010300033Q00201001030003000200201001030003000400066A010200100001000300049F012Q001000012Q007000025Q0020100102000200052Q005E0102000100012Q0024012Q00013Q0006930001001300013Q00049F012Q001300012Q0024012Q00013Q00201001023Q0006001220010300033Q002010010300030006002010010300030007000640010200260001000300049F012Q0026000100201001023Q0006001220010300033Q002010010300030006002010010300030008000640010200260001000300049F012Q0026000100201001023Q0006001220010300033Q002010010300030006002010010300030009000640010200260001000300049F012Q002600012Q001200026Q0065010200013Q0006FC0002002A0001000100049F012Q002A00012Q0024012Q00013Q00201001033Q000A2Q0070000400024Q0018010500034Q0070000600034Q008C0104000600020006930004003200013Q00049F012Q003200012Q0024012Q00014Q0070000400043Q00201001040004000B0006930004003D00013Q00049F012Q003D00012Q0070000400024Q0018010500034Q0070000600044Q008C0104000600020006930004003D00013Q00049F012Q003D00012Q0024012Q00014Q007000045Q0020100104000400052Q005E0104000100012Q0024012Q00017Q00033Q0003063Q004163746976650003063Q00616E63686F7201134Q007000015Q0020102Q01000100010006FC000100060001000100049F012Q000600012Q00652Q016Q00AA2Q0100023Q0026473Q000A0001000200049F012Q000A00012Q00652Q0100014Q00AA2Q0100024Q007000015Q0020102Q01000100010020102Q01000100030006402Q01001000013Q00049F012Q001000012Q001200016Q00652Q0100014Q00AA2Q0100024Q0024012Q00017Q00043Q0003053Q00436C6F736503073Q0044657374726F7903063Q00436C6F736564030D3Q00446973636F2Q6E656374412Q6C00124Q0045016Q00206Q00016Q000100016Q00018Q000100016Q00023Q00064Q000D00013Q00049F012Q000D00012Q00703Q00023Q0020115Q00022Q0004012Q000200012Q001E8Q0095012Q00024Q00707Q002010014Q00030020115Q00042Q0004012Q000200012Q0024012Q00017Q00203Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C03093Q00636F72652F4D61696403093Q00636F72652F5574696C030A3Q00636F72652F476C79706803093Q00636F72652F44726167030B3Q00636F72652F486F746B6579030D3Q00636F72652F506C6174666F726D030E3Q006F7665726C6179732F4C61796572030E3Q00636F6D706F6E656E74732F54616203073Q002Q5F696E64657803073Q00566563746F72322Q033Q006E6577025Q00807B40025Q00C07240025Q00208C40025Q0080864003093Q004E6578744F7264657203083Q00496E646578526F7703063Q00412Q6454616203073Q005365744F70656E03063Q00546F2Q676C6503063Q005365744B657903073Q0053657453746174030E3Q005365745472616E736C7563656E7403113Q004275696C644D6F62696C65546F2Q676C6503123Q006175726F72612F77696E646F772E6A736F6E030C3Q005361766547656F6D65747279030F3Q00526573746F726547656F6D6574727903073Q0044657374726F79016B4Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q00890004000200022Q001801055Q001291000600054Q00890005000200022Q006500065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q00122Q000900086Q0008000200024Q00095Q00122Q000A00096Q0009000200024Q000A5Q00122Q000B000A6Q000A000200024Q000B5Q00122Q000C000B6Q000B000200024Q000C5Q00122Q000D000C6Q000C000200024Q000D5Q00102Q000D000D000D001220010E000E3Q002010010E000E000F001291000F00103Q001291001000114Q008C010E00100002001220010F000E3Q002010010F000F000F001291001000123Q001291001100134Q008C010F001100020006D400103Q0001000D2Q0018012Q000D4Q0018012Q00054Q0018012Q00044Q0018012Q000A4Q0018012Q00014Q0018012Q00024Q0018012Q00074Q0018012Q00034Q0018012Q000B4Q0018012Q00084Q0018012Q000E4Q0018012Q000F4Q0018012Q00093Q001056000D000F0010000290011000013Q001056000D00140010000290011000023Q001056000D001500100006D400100003000100012Q0018012Q000C3Q001056000D001600100006D400100004000100032Q0018012Q000B4Q0018012Q00034Q0018012Q00023Q001056000D00170010000290011000053Q001056000D001800100006D400100006000100012Q0018012Q00093Q001056000D00190010000290011000073Q001056000D001A00100006D400100008000100012Q0018012Q00023Q001056000D001B00100006D400100009000100032Q0018012Q00014Q0018012Q00024Q0018012Q00083Q001056000D001C00100012910010001D3Q0006D40011000A000100022Q0018012Q000A4Q0018012Q00103Q001056000D001E00110006D40011000B000100052Q0018012Q000A4Q0018012Q00104Q0018012Q00064Q0018012Q000E4Q0018012Q000F3Q001056000D001F00110006D40011000C000100012Q0018012Q000B3Q001056000D002000112Q00AA010D00024Q0024012Q00013Q000D3Q009F3Q00030C3Q007365746D6574617461626C6503063Q004175726F726103043Q005461627303093Q004163746976655461620003043Q004D6169642Q033Q006E6577030A3Q005461624368616E67656403073Q00546F2Q676C656403043Q004F70656E2Q0103043Q00526F777303063Q005F6F72646572028Q00030C3Q005F7472616E736C7563656E74030B3Q005472616E736C7563656E74010003043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00208240025Q00607D4003083Q0049734D6F62696C652Q033Q004775692Q033Q004E657703093Q005363722Q656E47756903043Q004E616D6503073Q004775694E616D65030C3Q0052657365744F6E537061776E030E3Q005A496E6465784265686176696F7203043Q00456E756D03073Q005369626C696E67030C3Q00446973706C61794F72646572024Q008087C340030E3Q0049676E6F7265477569496E73657403063Q00506172656E7403093Q00477569506172656E7403043Q004769766503043Q00522Q6F7403053Q004672616D6503063Q0057696E646F77030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F03083Q00506F736974696F6E03093Q0066726F6D5363616C6503103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E03093Q00636F6C6F722E77696E03163Q004261636B67726F756E645472616E73706172656E637903093Q00616C7068612E77696E03103Q00436C69707344657363656E64616E747303063Q00436F726E65722Q033Q00476574030A3Q007261646975732E77696E03063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503053Q005363616C6503073Q0055495363616C65026Q00F03F03043Q004865616403093Q0073697A652E7461627303083Q005461625374726970026Q002C40025Q00C062C0030C3Q0055494C6973744C61796F7574030D3Q0046692Q6C446972656374696F6E030A3Q00486F72697A6F6E74616C03113Q00566572746963616C416C69676E6D656E7403063Q0043656E74657203073Q0050612Q64696E6703043Q005544696D026Q00304003093Q00536F72744F72646572030B3Q004C61796F75744F72646572030C3Q00536561726368486F6C64657203063Q00536561726368026Q0040C0026Q005A40026Q003440030A3Q00616C7068612E77652Q6C030A3Q007261646975732E63746C026Q00244003083Q00636F6C6F722E6C6F026Q001C4003093Q00536561726368426F7803043Q00546578742Q033Q00426F78026Q003640026Q003CC0034Q00030F3Q00506C616365686F6C6465725465787403063Q0073656172636803113Q00506C616365686F6C646572436F6C6F7233030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903103Q00436C656172546578744F6E466F63757303023Q00756903073Q0054657874426F78030B3Q00436C6F736542752Q746F6E030A3Q005465787442752Q746F6E03053Q00436C6F7365026Q0020C0026Q003240026Q00084003053Q0043726F2Q73026Q002240030A3Q004D6F757365456E74657203073Q00436F2Q6E656374030A3Q004D6F7573654C6561766503113Q004D6F75736542752Q746F6E31436C69636B03093Q0073697A652E662Q6F742Q033Q004D696403043Q00426F6479026Q0034C003073Q00436F6C756D6E41026Q0018C003073Q00436F6C756D6E42026Q00184003073Q0044697669646572027Q0040026Q0024C0030E3Q00616C7068612E6C696E65536F667403043Q00462Q6F7403043Q0053746174026Q002CC003043Q006D6F6E6F03063Q00437265646974026Q33E33F03063Q00462Q6F74657203053Q005469746C6503063Q006175726F7261030F3Q00202D206D6164652077697468203C33030E3Q005465787458416C69676E6D656E7403053Q00526967687403053Q00736D612Q6C03043Q0047726970027Q00C0026Q002840026Q001040026Q00144003083Q00526F746174696F6E025Q008046C0026Q66D63F03043Q00496E697403073Q004472612Q67657203063Q00412Q7461636803053Q006F6E456E6403073Q00526573697A657203063Q00526573697A6503093Q00546F2Q676C654B657903073Q004B6579436F6465030A3Q005269676874536869667403053Q005374617274030D3Q005F756E62696E64546F2Q676C6503043Q0042696E6403113Q004275696C644D6F62696C65546F2Q676C65030F3Q00526573746F726547656F6D6574727902F0022Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q001220010200014Q002A01036Q007000046Q008C010200040002001056000200024Q002A01035Q0010560002000300030030050002000400052Q0070000300013Q0020100103000300072Q00F20003000100020010560002000600032Q0070000300023Q0020100103000300072Q00F20003000100020010560002000800032Q0070000300023Q0020100103000300072Q00F20003000100020010560002000900030030050002000A000B2Q002A01035Q0010560002000C00030030050002000D000E002010010300010010002647000300200001001100049F012Q002000012Q001200036Q0065010300013Q0010560002000F00030020100103000100120006FC0003002A0001000100049F012Q002A0001001220010300133Q002010010300030014001291000400153Q001291000500164Q008C0103000500022Q0070000400033Q0020100104000400172Q00F20004000100022Q0070000500043Q0020100105000500190012910006001A4Q002A01073Q000600201001080001001C0006FC000800350001000100049F012Q00350001001291000800023Q0010560007001B00080030050007001D00110012200108001F3Q00201001080008001E0020100108000800200010560007001E00080020100108000100210006FC0008003F0001000100049F012Q003F0001001291000800223Q00105600070021000800300500070023000B2Q0070000800033Q0020100108000800252Q00F20008000100020010560007002400082Q008C0105000700020010560002001800050020100105000200060020110005000500260020100107000200182Q004D0105000700012Q006B000500043Q00202Q00050005001900122Q000600286Q00073Q000800302Q0007001B002900122Q0008002B3Q00202Q00080008000700122Q0009002C3Q00122Q000A002C6Q0008000A00020010560007002A000800201001080001002D0006FC0008005E0001000100049F012Q005E0001001220010800133Q00201001080008002E0012910009002C3Q001291000A002C4Q008C0108000A00020010560007002D00080010560007001200032Q0070000800043Q002010010800080030001291000900314Q00890008000200020010560007002F00080020100108000100100026470008006B0001001100049F012Q006B00010012910008000E3Q0006FC0008006F0001000100049F012Q006F00012Q0070000800043Q002010010800080030001291000900334Q00890008000200020010560007003200080030050007003400110020100108000200180010560007002400082Q008C0105000700020010560002002700052Q0070000500043Q0020100105000500352Q0070000600053Q002010010600060036001291000700374Q008900060002000200209D0107000200274Q0005000700014Q000500043Q00202Q00050005003800202Q00060002002700122Q000700393Q00122Q0008003A6Q0005000800014Q000500043Q00202Q0005000500190012910006003C4Q002A01073Q00020030050007003B003D0020100108000200270010560007002400082Q008C0105000700020010560002003B00052Q0070000500043Q002010010500050019001291000600284Q002A01073Q00040030050007001B003E001220010800133Q0020100108000800070012910009003D3Q001291000A000E3Q001291000B000E4Q0070000C00053Q002010010C000C0036001291000D003F4Q00F6000C000D4Q007301083Q000200105600070012000800300500070032003D0020100108000200270010560007002400082Q008C0105000700020010560002003E00052Q006B000500043Q00202Q00050005001900122Q000600286Q00073Q000500302Q0007001B000300122Q000800133Q00202Q00080008001400122Q000900413Q00122Q000A000E6Q0008000A00020010560007002D0008001220010800133Q0020100108000800070012910009003D3Q001291000A00423Q001291000B003D3Q001291000C000E4Q008C0108000C000200105600070012000800300500070032003D00201001080002003E0010560007002400082Q008C0105000700020010560002004000052Q0070000500043Q002010010500050019001291000600434Q002A01073Q00050012200108001F3Q0020100108000800440020100108000800450010560007004400080012200108001F3Q002010010800080046002010010800080047001056000700460008001220010800493Q0020100108000800070012910009000E3Q001291000A004A4Q008C0108000A00020010560007004800080012200108001F3Q00201001080008004B00201001080008004C0010560007004B00080020100108000200400010560007002400082Q004D0105000700012Q006B000500043Q00202Q00050005001900122Q000600286Q00073Q000700302Q0007001B004E00122Q0008002B3Q00202Q00080008000700122Q0009003D3Q00122Q000A002C6Q0008000A00020010560007002A0008001220010800133Q0020100108000800070012910009003D3Q0012D5000A004F3Q00122Q000B002C3Q00122Q000C000E6Q0008000C000200102Q0007002D000800122Q000800133Q00202Q00080008001400122Q000900503Q00122Q000A00516Q0008000A00020010560007001200082Q0070000800043Q002010010800080030001291000900394Q00890008000200020010560007002F00082Q0070000800043Q002010010800080030001291000900524Q008900080002000200105600070032000800201001080002003E0010560007002400082Q008C0105000700020010560002004D00052Q0070000500043Q0020100105000500352Q0070000600053Q002010010600060036001291000700534Q008900060002000200201901070002004D4Q0005000700014Q000500063Q00202Q00050005004E00202Q00060002004D00122Q000700543Q00122Q000800556Q00050008000200122Q0006002B3Q00202Q0006000600070012910007000E3Q0012E50008002C6Q00060008000200102Q0005002A000600122Q000600133Q00202Q00060006000700122Q0007000E3Q00122Q000800563Q00122Q0009002C3Q00122Q000A000E6Q0006000A00020010560005002D00062Q0070000600043Q0020100106000600582Q002A01073Q00090030B30007001B005900122Q000800133Q00202Q00080008001400122Q0009005A3Q00122Q000A000E6Q0008000A000200102Q0007002D000800122Q000800133Q00202Q00080008000700122Q0009003D3Q001291000A005B3Q001291000B003D3Q001291000C000E4Q008C0108000C000200105600070012000800304E00070058005C00302Q0007005D005E4Q000800053Q00202Q00080008003600122Q000900556Q00080002000200102Q0007005F00084Q000800043Q00202Q00080008003000122Q000900614Q008900080002000200105600070060000800300500070062001100201001080002004D001056000700240008001291000800633Q0012F8000900646Q00060009000200102Q0002005700064Q000600043Q00202Q00060006001900122Q000700666Q00083Q000800302Q0008001B006700122Q0009002B3Q00202Q000900090007001291000A003D3Q0012E5000B002C6Q0009000B000200102Q0008002A000900122Q000900133Q00202Q00090009000700122Q000A003D3Q00122Q000B00683Q00122Q000C002C3Q00122Q000D000E6Q0009000D00020010560008002D0009001220010900133Q002010010900090014001291000A00693Q001291000B00694Q008C0109000B00020010560008001200092Q0070000900043Q002010010900090030001291000A00394Q00890009000200020010560008002F000900300500080032003D00300500080058005C00201001090002003E0010560008002400092Q008C0106000800020010560002006500062Q0070000600043Q0020100106000600350012910007006A3Q0020190108000200654Q0006000800014Q000600063Q00202Q00060006006B00202Q00070002006500122Q0008006C3Q00122Q000900556Q00060009000200122Q0007002B3Q00202Q0007000700070012910008002C3Q0012910009002C4Q008C0107000900020010560006002A0007001220010700133Q00201001070007002E0012910008002C3Q0012910009002C4Q008C0107000900020010560006002D000700200400070002000600202Q00070007002600202Q00090002006500202Q00090009006D00202Q00090009006E0006D4000B3Q000100042Q00703Q00074Q0018012Q00024Q00703Q00054Q0018012Q00064Q003C0109000B6Q00073Q000100202Q00070002000600202Q00070007002600202Q00090002006500202Q00090009006F00202Q00090009006E0006D4000B0001000100042Q00703Q00074Q0018012Q00024Q0018012Q00064Q00703Q00054Q003C0109000B6Q00073Q000100202Q00070002000600202Q00070007002600202Q00090002006500202Q00090009007000202Q00090009006E0006D4000B0002000100012Q0018012Q00024Q00090009000B6Q00073Q00014Q000700053Q00202Q00070007003600122Q000800716Q0007000200024Q000800043Q00202Q00080008001900122Q000900286Q000A3Q000500302Q000A001B007300122Q000B00133Q00202Q000B000B001400122Q000C00546Q000D00053Q00202Q000D000D003600122Q000E003F6Q000D000E6Q000B3Q000200102Q000A002D000B00122Q000B00133Q00202Q000B000B000700122Q000C003D3Q00122Q000D00743Q00122Q000E003D6Q000F00053Q00202Q000F000F003600122Q0010003F6Q000F000200024Q000F000F6Q000F000F00074Q000B000F000200102Q000A0012000B00302Q000A0032003D00202Q000B0002002700102Q000A0024000B4Q0008000A000200102Q0002007200080006D400080003000100032Q00703Q00044Q00703Q00054Q0018012Q00024Q0048000900083Q00122Q000A00753Q00122Q000B000E3Q00122Q000C000E3Q00122Q000D00766Q0009000D000200102Q0002007500094Q000900083Q00122Q000A00773Q00122Q000B002C3Q001291000C00783Q0012F8000D00766Q0009000D000200102Q0002007700094Q000900043Q00202Q00090009001900122Q000A00286Q000B3Q000700302Q000B001B007900122Q000C002B3Q00202Q000C000C0007001291000D002C3Q0012E5000E000E6Q000C000E000200102Q000B002A000C00122Q000C00133Q00202Q000C000C000700122Q000D002C3Q00122Q000E000E3Q00122Q000F000E3Q00122Q0010007A6Q000C00100002001056000B002D000C00123F010C00133Q00202Q000C000C000700122Q000D000E3Q00122Q000E003D3Q00122Q000F003D3Q00122Q0010007B6Q000C0010000200102Q000B0012000C4Q000C00043Q00202Q000C000C0030001291000D00394Q0089000C00020002001056000B002F000C2Q0070000C00043Q002010010C000C0030001291000D007C4Q0089000C00020002001052000B0032000C00202Q000C0002007200102Q000B0024000C4Q0009000B000200102Q0002007900094Q000900043Q00202Q00090009001900122Q000A00286Q000B3Q000600302Q000B001B007D001220010C002B3Q002010010C000C0007001291000D000E3Q0012E5000E003D6Q000C000E000200102Q000B002A000C00122Q000C00133Q00202Q000C000C000700122Q000D000E3Q00122Q000E000E3Q00122Q000F003D3Q00122Q0010000E6Q000C00100002001056000B002D000C001220010C00133Q002010010C000C0007001291000D003D3Q001291000E000E3Q001291000F000E4Q0018011000074Q008C010C001000020010FA000B0012000C00302Q000B0032003D00202Q000C0002002700102Q000B0024000C4Q0009000B000200102Q0002007D00094Q000900043Q00202Q0009000900584Q000A3Q000600302Q000A001B007E00122Q000B00133Q00202Q000B000B001400122Q000C00413Q00122Q000D000E6Q000B000D000200102Q000A002D000B00122Q000B00133Q00202Q000B000B000700122Q000C002C3Q00122Q000D007F3Q00122Q000E003D3Q00122Q000F000E6Q000B000F000200102Q000A0012000B00302Q000A0058005C4Q000B00043Q00202Q000B000B003000122Q000C00556Q000B0002000200102Q000A0060000B00202Q000B0002007D00102Q000A0024000B00122Q000B00806Q0009000B000200102Q0002007E00094Q000900043Q00202Q0009000900584Q000A3Q000800302Q000A001B008100122Q000B002B3Q00202Q000B000B000700122Q000C003D3Q00122Q000D000E6Q000B000D000200102Q000A002A000B00122Q000B00133Q00202Q000B000B000700122Q000C003D3Q00122Q000D007F3Q00122Q000E000E3Q00122Q000F000E6Q000B000F000200102Q000A002D000B00122Q000B00133Q00202Q000B000B000700122Q000C00823Q00122Q000D007F3Q00122Q000E003D3Q00122Q000F000E6Q000B000F000200102Q000A0012000B00202Q000B0001008300062Q000B00550201000100049F012Q00550201002010010B000100840006FC000B00530201000100049F012Q00530201001291000B00853Q001291000C00864Q006B010B000B000C001056000A0058000B2Q0076010B00043Q00202Q000B000B003000122Q000C00556Q000B0002000200102Q000A0060000B00122Q000B001F3Q00202Q000B000B008700202Q000B000B008800102Q000A0087000B00202Q000B0002007D00102Q000A0024000B00122Q000B00896Q0009000B000200102Q0002008100094Q000900043Q00202Q00090009001900122Q000A00666Q000B3Q000700302Q000B001B008A00122Q000C002B3Q00202Q000C000C000700122Q000D003D3Q00122Q000E003D6Q000C000E000200102Q000B002A000C00122Q000C00133Q00202Q000C000C000700122Q000D003D3Q00122Q000E008B3Q00122Q000F003D3Q00122Q0010008B6Q000C0010000200102Q000B002D000C00122Q000C00133Q00202Q000C000C001400122Q000D008C3Q00122Q000E008C6Q000C000E000200102Q000B0012000C00302Q000B0032003D00302Q000B0058005C00202Q000C0002002700102Q000B0024000C4Q0009000B000200102Q0002008A000900122Q0009003D3Q00122Q000A007A3Q00122Q000B003D3Q00042Q000900B102012Q0070000D00043Q002010010D000D00190012DF000E00286Q000F3Q000700122Q0010002B3Q00202Q00100010000700122Q0011003D3Q00122Q0012003D6Q00100012000200102Q000F002A001000122Q001000133Q00202Q0010001000070012910011003D3Q0012910012000E3Q0012910013003D3Q00203E0014000C003D2Q0085011400143Q00201F01140014008D2Q008C011000140002001056000F002D0010001220011000133Q002010011000100014002647000C00A20201003D00049F012Q00A20201001291001100543Q0006FC001100A30201000100049F012Q00A302010012910011008E3Q0012910012003D4Q001F00100012000200102Q000F0012001000302Q000F008F00904Q001000043Q00202Q00100010003000122Q001100556Q00100002000200102Q000F002F001000302Q000F0032009100202Q00100002008A001056000F002400102Q004D010D000F00010004510009008702012Q0070000900083Q002010010900090092002010010A000200272Q00040109000200012Q0070000900093Q002010010900090094002010010A0002003E002010010B000200272Q002A010C3Q00010006D4000D0004000100012Q0018012Q00023Q001056000C0095000D2Q008C0109000C0002001056000200930009002010010900020006002011000900090026002010010B000200932Q004D0109000B00012Q0070000900093Q002010010900090097002010010A0002008A002010010B000200272Q0070000C000A4Q0070000D000B4Q002A010E3Q00010006D4000F0005000100012Q0018012Q00023Q001094010E0095000F4Q0009000E000200102Q00020096000900202Q00090002000600202Q00090009002600202Q000B000200964Q0009000B000100202Q00090001009800062Q000900D90201000100049F012Q00D902010012200109001F3Q00201001090009009900201001090009009A0010560002009800092Q001B0009000C3Q00202Q00090009009B4Q0009000100014Q0009000C3Q00202Q00090009009D00202Q000A000200980006D4000B0006000100012Q0018012Q00024Q008C0109000B00020010560002009C0009002010010900020006002011000900090026002010010B0002009C2Q004D0109000B0001000693000400EC02013Q00049F012Q00EC020100201100090002009E2Q000401090002000100201100090002009F2Q00040109000200012Q00AA010200024Q0024012Q00013Q00073Q00073Q0003053Q0054772Q656E030B3Q00436C6F736542752Q746F6E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030A3Q00616C7068612E77652Q6C03083Q00536574436F6C6F7203083Q00636F6C6F722E686900134Q008F016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q00014Q000300023Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200016Q00033Q00206Q00064Q000100023Q00202Q00010001000400122Q000200076Q000100029Q0000016Q00017Q00073Q0003053Q0054772Q656E030B3Q00436C6F736542752Q746F6E03163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03083Q00536574436F6C6F722Q033Q0047657403083Q00636F6C6F722E6C6F000F4Q0096016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q000100302Q0002000300046Q000200016Q00023Q00206Q00054Q000100033Q00202Q00010001000600122Q000200076Q000100029Q0000016Q00017Q00013Q0003073Q005365744F70656E00054Q00707Q0020115Q00012Q006501026Q004D012Q000200012Q0024012Q00017Q00223Q002Q033Q004E6577030E3Q005363726F2Q6C696E674672616D6503043Q004E616D6503083Q00506F736974696F6E03053Q005544696D322Q033Q006E6577028Q00027Q004003043Q0053697A65026Q00E03F026Q00F03F026Q0024C0030A3Q0043616E76617353697A6503133Q004175746F6D6174696343616E76617353697A6503043Q00456E756D030D3Q004175746F6D6174696353697A6503013Q005903123Q005363726F2Q6C426172546869636B6E652Q732Q033Q00476574030E3Q0073697A652E7363726F2Q6C62617203143Q005363726F2Q6C426172496D616765436F6C6F723303083Q00636F6C6F722E6C6F031A3Q005363726F2Q6C426172496D6167655472616E73706172656E637902CD5QCCDC3F03063Q00506172656E742Q033Q004D6964030C3Q0055494C6973744C61796F757403073Q0050612Q64696E6703043Q005544696D03083Q0073697A652E67617003093Q00536F72744F72646572030B3Q004C61796F75744F72646572026Q001840026Q00104004494Q007000045Q002010010400040001001291000500024Q002A01063Q0009001056000600033Q001220010700053Q0020100107000700062Q0018010800014Q0018010900023Q001291000A00073Q001291000B00084Q008C0107000B0002001056000600040007001220010700053Q0020100107000700060012910008000A4Q0018010900033Q001291000A000B3Q001291000B000C4Q008C0107000B0002001056000600090007001220010700053Q0020100107000700062Q00F20007000100020010560006000D00070012200107000F3Q00201001070007001000206801070007001100102Q0006000E00074Q000700013Q00202Q00070007001300122Q000800146Q00070002000200102Q0006001200074Q000700013Q00202Q00070007001300122Q000800164Q00890007000200020010560006001500070030050006001700182Q0070000700023Q00201001070007001A0010560006001900072Q008C0104000600022Q007000055Q0020100105000500010012910006001B4Q002A01073Q00030012200108001D3Q002010010800080006001291000900074Q0070000A00013Q002010010A000A0013001291000B001E4Q00F6000A000B4Q007301083Q00020010560007001C00080012200108000F3Q00201001080008001F0020100108000800200010560007001F00080010560007001900042Q004D0105000700012Q007000055Q00201001050005001C2Q0018010600043Q001291000700213Q001291000800223Q001291000900213Q001291000A00074Q004D0105000A00012Q00AA010400024Q0024012Q00017Q00013Q00030C3Q005361766547656F6D6574727900044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00013Q00030C3Q005361766547656F6D6574727900044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00023Q0003053Q00626567616E03063Q00546F2Q676C6501063Q0026473Q00050001000100049F012Q000500012Q007000015Q0020110001000100022Q00042Q01000200012Q0024012Q00017Q00023Q0003063Q005F6F72646572026Q00F03F01063Q0020992Q013Q000100202Q00010001000200104Q0001000100202Q00013Q00014Q000100028Q00017Q00053Q0003043Q00526F7773026Q00F03F2Q033Q00526F7703083Q0047726F7570626F782Q033Q00546162030B3Q00201001033Q000100201001043Q00012Q0001000400043Q0020600004000400022Q002A01053Q00030010560005000300010010560005000400020020100106000200050010560005000500062Q004A0103000400052Q0024012Q00017Q00073Q002Q033Q006E657703043Q0054616273026Q00F03F03043Q004D61696403043Q0047697665030B3Q0053657453656C656374656403093Q0041637469766554616203194Q005400035Q00202Q0003000300014Q00048Q000500016Q000600026Q00030006000200202Q00043Q000200202Q00053Q00024Q000500053Q00202Q0005000500034Q00040005000300202Q00043Q000400202Q0004000400054Q000600036Q00040006000100202Q00043Q00024Q000400043Q00262Q000400170001000300049F012Q001700010020110004000300062Q0065010600014Q004D0104000600010010563Q000700032Q00AA010300024Q0024012Q00017Q00143Q0003043Q004F70656E03053Q00436C6F736503043Q00522Q6F7403073Q0056697369626C6503053Q005363616C65026Q00F03F2Q010285EB51B81E85EF3F03053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E6379030C3Q005F7472616E736C7563656E740100028Q002Q033Q0047657403093Q00616C7068612E77696E03043Q007461736B03053Q0064656C617903083Q004475726174696F6E03073Q00546F2Q676C656403043Q004669726503493Q0006930001000500013Q00049F012Q000500012Q0065010300013Q00060B2Q0100060001000300049F012Q000600012Q00652Q015Q00201001033Q000100066A2Q01000C0001000300049F012Q000C00010006FC0002000C0001000100049F012Q000C00012Q00AA012Q00023Q0010563Q000100010006FC000100120001000100049F012Q001200012Q007000035Q0020100103000300022Q005E0103000100010006930002001900013Q00049F012Q0019000100201001033Q000300105600030004000100201001033Q000500300500030005000600049F012Q004300010006930001003600013Q00049F012Q0036000100201001033Q000300300500030004000700201001033Q00050030050003000500082Q0070000300013Q00201001030003000900201001043Q00052Q002A01053Q00010030050005000500062Q004D0103000500012Q0070000300013Q00200201030003000900202Q00043Q00034Q00053Q000100202Q00063Q000B00262Q0006002F0001000C00049F012Q002F00010012910006000D3Q0006FC000600330001000100049F012Q003300012Q0070000600023Q00201001060006000E0012910007000F4Q00890006000200020010560005000A00062Q004D01030005000100049F012Q004300012Q0070000300013Q00201001030003000900201001043Q00052Q002A01053Q00010030050005000500082Q004D010300050001001220010300103Q0020100103000300112Q0070000400013Q0020100104000400120006D400053Q000100012Q0018017Q004D01030005000100201001033Q00130020110003000300142Q0018010500014Q004D0103000500012Q00AA012Q00024Q0024012Q00013Q00013Q00043Q0003043Q004F70656E03043Q00522Q6F7403073Q0056697369626C65012Q00084Q00707Q002010014Q00010006FC3Q00070001000100049F012Q000700012Q00707Q002010014Q00020030053Q000300042Q0024012Q00017Q00023Q0003073Q005365744F70656E03043Q004F70656E01063Q00201100013Q000100201001033Q00022Q005F000300034Q00562Q0100034Q003500016Q0024012Q00017Q00053Q00030D3Q005F756E62696E64546F2Q676C6503093Q00546F2Q676C654B657903043Q0042696E6403043Q004D61696403043Q004769766502133Q00201001023Q00010006930002000500013Q00049F012Q0005000100201001023Q00012Q005E0102000100010010563Q000200012Q007000025Q0020100102000200032Q0018010300013Q0006D400043Q000100012Q0018017Q005900020004000200104Q0001000200202Q00023Q000400202Q00020002000500202Q00043Q00014Q0002000400016Q00028Q00013Q00013Q00023Q0003053Q00626567616E03063Q00546F2Q676C6501063Q0026473Q00050001000100049F012Q000500012Q007000015Q0020110001000100022Q00042Q01000200012Q0024012Q00017Q00043Q0003043Q005374617403043Q005465787403083Q00746F737472696E67034Q0002093Q00201001023Q0001001220010300033Q00060B010400050001000100049F012Q00050001001291000400044Q00890003000200020010560002000200032Q00AA012Q00024Q0024012Q00017Q00063Q00030C3Q005F7472616E736C7563656E7403043Q00522Q6F7403163Q004261636B67726F756E645472616E73706172656E63792Q033Q0047657403093Q00616C7068612E77696E028Q00020E3Q0010563Q0001000100201001023Q00020006930001000A00013Q00049F012Q000A00012Q007000035Q002010010300030004001291000400054Q00890003000200020006FC0003000B0001000100049F012Q000B0001001291000300063Q0010560002000300032Q00AA012Q00024Q0024012Q00017Q00293Q00030C3Q004D6F62696C6542752Q746F6E2Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503063Q00546F2Q676C6503083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q002C40026Q005E4003043Q0053697A65026Q004840026Q003A4003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E03093Q00636F6C6F722E77696E03163Q004261636B67726F756E645472616E73706172656E637903093Q00616C7068612E77696E03043Q0054657874034Q0003063Q00506172656E742Q033Q0047756903063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503093Q0066726F6D5363616C65026Q00F03F03043Q006D656E75030A3Q0054657874436F6C6F723303083Q00636F6C6F722E6869030E3Q005465787458416C69676E6D656E7403043Q00456E756D03063Q0043656E74657203043Q004D61696403043Q004769766503063Q00412Q7461636803113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E65637401564Q006B00015Q00202Q00010001000200122Q000200036Q00033Q000700302Q00030004000500122Q000400073Q00202Q00040004000800122Q000500093Q00122Q0006000A6Q000400060002001056000300060004001220010400073Q0020100104000400080012910005000C3Q0012910006000D4Q008C0104000600020010560003000B00042Q007000045Q00203C00040004000F00122Q000500106Q00040002000200102Q0003000E00044Q00045Q00202Q00040004000F00122Q000500126Q00040002000200102Q00030011000400302Q00030013001400201001043Q00160010560003001500042Q008C2Q01000300020010563Q000100012Q007000015Q0020102Q01000100172Q0070000200013Q002010010200020018001291000300194Q008900020002000200209D01033Q00014Q0001000300014Q00015Q00202Q00010001001A00202Q00023Q000100122Q0003001B3Q00122Q0004001C6Q0001000400014Q00015Q00202Q0001000100132Q002A01023Q0005001220010300073Q00201001030003001D0012910004001E3Q0012910005001E4Q008C0103000500020010560002000B000300300500020013001F2Q007000035Q00201001030003000F001291000400214Q0089000300020002001056000200200003001220010300233Q00201001030003002200201001030003002400105600020022000300201001033Q00010010560002001500032Q00042Q01000200010020102Q013Q00250020110001000100262Q0070000300023Q00201001030003002700201001043Q000100201001053Q00012Q003C010300056Q00013Q000100202Q00013Q002500202Q00010001002600202Q00033Q000100202Q00030003002800202Q0003000300290006D400053Q000100012Q0018017Q0072010300054Q00612Q013Q00012Q0024012Q00013Q00013Q00013Q0003063Q00546F2Q676C6500044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00063Q0003043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q74705365727669636503053Q007063612Q6C03073Q0053746F7261676503053Q00577269746501123Q0012202Q0100013Q002011000100010002001291000300034Q008C2Q0100030002001220010200043Q0006D400033Q000100022Q0018012Q00014Q0018017Q005E0002000200030006930002001100013Q00049F012Q001100012Q007000045Q00207401040004000500202Q0004000400064Q000500016Q000600036Q0004000600012Q0024012Q00013Q00013Q000E3Q00030A3Q004A534F4E456E636F646503013Q007803043Q00522Q6F7403083Q00506F736974696F6E03013Q005803063Q004F2Q6673657403013Q007903013Q005903023Q00787303053Q005363616C6503023Q00797303013Q007703043Q0053697A6503013Q0068002A4Q00707Q0020115Q00012Q002A01023Q00062Q0070000300013Q0020100103000300030020100103000300040020100103000300050020100103000300060010560002000200032Q0070000300013Q0020100103000300030020100103000300040020100103000300080020100103000300060010560002000700032Q0070000300013Q00201001030003000300201001030003000400201001030003000500201001030003000A0010560002000900032Q0070000300013Q00201001030003000300201001030003000400201001030003000800201001030003000A0010560002000B00032Q0070000300013Q00201001030003000300201001030003000D0020100103000300050020100103000300060010560002000C00032Q0070000300013Q00201001030003000300201001030003000D0020100103000300080020100103000300060010560002000E00032Q0056012Q00024Q00358Q0024012Q00017Q00183Q0003073Q0053746F7261676503043Q005265616403043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q74705365727669636503053Q007063612Q6C03043Q007479706503053Q007461626C6503013Q007703013Q006803043Q00522Q6F7403043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403053Q00636C616D7003013Q005803013Q005903013Q007803013Q007903083Q00506F736974696F6E2Q033Q006E657703023Q007873026Q00E03F03023Q007973014A4Q006900015Q00202Q00010001000100202Q0001000100024Q000200016Q00010002000200062Q000100080001000100049F012Q000800012Q0024012Q00013Q001220010200033Q002011000200020004001291000400054Q008C010200040002001220010300063Q0006D400043Q000100022Q0018012Q00024Q0018012Q00014Q005E0003000200040006930003001800013Q00049F012Q00180001001220010500074Q0018010600044Q0089000500020002002696000500190001000800049F012Q001900012Q0024012Q00013Q0020100105000400090006930005003400013Q00049F012Q0034000100201001050004000A0006930005003400013Q00049F012Q0034000100201001053Q000B0012200106000D3Q00201001060006000E2Q0070000700023Q00201001070007000F0020100108000400092Q0070000900033Q0020100109000900102Q0070000A00043Q002010010A000A00102Q008C0107000A00022Q0070000800023Q00201001080008000F00201001090004000A2Q0070000A00033Q002010010A000A00112Q0070000B00043Q002010010B000B00112Q00720108000B4Q007301063Q00020010560005000C00060020100105000400120006930005004900013Q00049F012Q004900010020100105000400130006930005004900013Q00049F012Q0049000100201001053Q000B0012200106000D3Q0020100106000600150020100107000400160006FC000700410001000100049F012Q00410001001291000700173Q0020100108000400120020100109000400180006FC000900460001000100049F012Q00460001001291000900173Q002010010A000400132Q008C0106000A00020010560005001400062Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E4465636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00093Q00030D3Q005F756E62696E64546F2Q676C6503073Q0044657374726F7903043Q004D616964030A3Q00446F436C65616E696E6703043Q005461627303043Q00526F7773030A3Q005461624368616E676564030D3Q00446973636F2Q6E656374412Q6C03073Q00546F2Q676C656401163Q0020102Q013Q00010006930001000500013Q00049F012Q000500010020102Q013Q00012Q005E2Q01000100012Q007000015Q0020E20001000100024Q00010001000100202Q00013Q000300202Q0001000100044Q0001000200014Q00015Q00104Q000500014Q00015Q00104Q0006000100202Q00013Q000700202Q0001000100084Q00010002000100202Q00013Q000900202Q0001000100084Q0001000200016Q00017Q00083Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C03093Q00636F72652F4D61696403133Q00636F6D706F6E656E74732F47726F7570626F7803073Q002Q5F696E6465782Q033Q006E6577011F4Q006C00015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00102Q0007000700070006D400083Q000100072Q0018012Q00074Q0018012Q00054Q0018012Q00044Q0018012Q00014Q0018012Q00024Q0018012Q00034Q0018012Q00063Q0010560007000800082Q00AA010700024Q0024012Q00013Q00013Q00393Q00030C3Q007365746D6574617461626C6503063Q0057696E646F7703043Q004E616D6503053Q00426F78657303083Q0053656C6563746564010003043Q004D6169642Q033Q006E657703073Q004368616E67656403063Q0042752Q746F6E2Q033Q004E6577030A3Q005465787442752Q746F6E03043Q005461625F03043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q002440026Q003440030D3Q004175746F6D6174696353697A6503043Q00456E756D03013Q005803163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03043Q0054657874034Q00030B3Q004C61796F75744F7264657203043Q005461627303063Q00506172656E7403083Q00546162537472697003043Q004769766503053Q004C6162656C028Q00030A3Q0054657874436F6C6F723303053Q00546F6B656E03093Q00636F6C6F722E6D69642Q033Q0074616203053Q00436F756E7403083Q00506F736974696F6E026Q000840026Q002C40030C3Q00636F6C6F722E612Q63656E7403073Q0056697369626C6503043Q006D6F6E6F03063Q005F7061696E7403073Q00436F2Q6E65637403113Q004D6F75736542752Q746F6E31436C69636B030A3Q004D6F757365456E746572030A3Q004D6F7573654C65617665030B3Q005265676973746572426F78030B3Q00412Q6447726F7570626F78030A3Q00412Q6453656374696F6E030F3Q00412Q644C65667447726F7570626F7803103Q00412Q64526967687447726F7570626F7803063Q0053656C656374030B3Q0053657453656C6563746564030D3Q005365744D61746368436F756E7403073Q0044657374726F7903B43Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q008E00048Q00058Q00030005000200102Q000300023Q00102Q0003000300014Q00045Q00102Q00030004000400302Q0003000500064Q000400013Q00202Q0004000400084Q00040001000200102Q0003000700044Q000400023Q00202Q0004000400084Q00040001000200102Q0003000900044Q000400033Q00202Q00040004000B00122Q0005000C6Q00063Q000700122Q0007000D6Q000800016Q00070007000800102Q00060003000700122Q0007000F3Q00202Q00070007001000122Q000800113Q00122Q000900126Q00070009000200102Q0006000E000700122Q000700143Q00202Q00070007001300202Q00070007001500102Q00060013000700302Q00060016001700302Q00060018001900202Q00073Q001B4Q000700073Q00202Q00070007001700102Q0006001A000700202Q00073Q001D00102Q0006001C00074Q00040006000200102Q0003000A000400202Q00040003000700202Q00040004001E00202Q00060003000A4Q0004000600014Q000400033Q00202Q0004000400184Q00053Q000600302Q00050003001800122Q0006000F3Q00202Q00060006000800122Q000700203Q00122Q000800203Q00122Q000900173Q00122Q000A00206Q0006000A000200102Q0005000E000600122Q000600143Q00202Q00060006001300202Q00060006001500102Q00050013000600102Q0005001800014Q000600033Q00202Q00060006002200122Q000700236Q00060002000200102Q00050021000600202Q00060003000A00102Q0005001C000600122Q000600246Q00040006000200102Q0003001F00044Q000400033Q00202Q0004000400184Q00053Q000700302Q00050003002500122Q0006000F3Q0020100106000600080012A9000700173Q00122Q000800273Q00122Q000900203Q00122Q000A00206Q0006000A000200102Q00050026000600122Q0006000F3Q00202Q00060006001000122Q000700283Q00122Q000800126Q00060008000200102Q0005000E000600302Q0005001800194Q000600033Q00202Q00060006002200122Q000700296Q00060002000200102Q00050021000600302Q0005002A000600202Q00060003000A00102Q0005001C000600122Q0006002B6Q00040006000200102Q0003002500040006D400043Q000100032Q0018012Q00034Q00703Q00044Q00703Q00053Q0010280103002C000400202Q00050003000700202Q00050005001E4Q000700043Q00202Q00070007000900202Q00070007002D4Q000900046Q000700096Q00053Q000100200400050003000700202Q00050005001E00202Q00070003000A00202Q00070007002E00202Q00070007002D0006D400090001000100012Q0018012Q00034Q003C010700096Q00053Q000100202Q00050003000700202Q00050005001E00202Q00070003000A00202Q00070007002F00202Q00070007002D0006D400090002000100032Q0018012Q00034Q00703Q00054Q00703Q00044Q003C010700096Q00053Q000100202Q00050003000700202Q00050005001E00202Q00070003000A00202Q00070007003000202Q00070007002D0006D400090003000100032Q0018012Q00034Q00703Q00054Q00703Q00044Q0072010700094Q006101053Q0001000290010500043Q0010560003003100050006D400050005000100012Q00703Q00063Q001056000300320005002010010500030032001056000300330005000290010500063Q001056000300340005000290010500073Q001056000300350005000290010500083Q0010560003003600050006D400050009000100012Q0018012Q00043Q0010560003003700050006D40005000A000100022Q00703Q00054Q00703Q00043Q0010560003003800050002900105000B3Q00100B0003003900054Q000500046Q0005000100014Q000300028Q00013Q000C3Q00073Q0003083Q0053656C65637465642Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403093Q00636F6C6F722E6D696403053Q0054772Q656E03053Q004C6162656C030A3Q0054657874436F6C6F723300164Q00707Q002010014Q00010006933Q000A00013Q00049F012Q000A00012Q00703Q00013Q002010014Q0002001291000100034Q00893Q000200020006FC3Q000E0001000100049F012Q000E00012Q00703Q00013Q002010014Q0002001291000100044Q00893Q000200022Q0070000100023Q0020102Q01000100052Q007000025Q0020100102000200062Q002A01033Q0001001056000300074Q004D2Q01000300012Q0024012Q00017Q00013Q0003063Q0053656C65637400044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00063Q0003083Q0053656C656374656403053Q0054772Q656E03053Q004C6162656C030A3Q0054657874436F6C6F72332Q033Q0047657403083Q00636F6C6F722E686900114Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002078014Q00024Q00015Q00202Q0001000100034Q00023Q00014Q000300023Q00202Q00030003000500122Q000400066Q00030002000200102Q0002000400036Q000200016Q00017Q00063Q0003083Q0053656C656374656403053Q0054772Q656E03053Q004C6162656C030A3Q0054657874436F6C6F72332Q033Q0047657403093Q00636F6C6F722E6D696400114Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002078014Q00024Q00015Q00202Q0001000100034Q00023Q00014Q000300023Q00202Q00030003000500122Q000400066Q00030002000200102Q0002000400036Q000200016Q00017Q00043Q0003053Q00426F786573026Q00F03F030A3Q0053657456697369626C6503083Q0053656C656374656402093Q00201001023Q000100201001033Q00012Q0001000300033Q0020600003000300022Q004A01020003000100201100020001000300201001043Q00042Q004D0102000400012Q0024012Q00017Q00093Q0003043Q007479706503063Q00737472696E6703013Q006103013Q006203053Q00426F786573027Q0040028Q002Q033Q006E657703053Q0067726F757004263Q001220010700014Q0018010800014Q00890007000200020026470007000F0001000200049F012Q000F0001002696000100090001000300049F012Q000900010026470001000F0001000400049F012Q000F00012Q0018010700014Q00AB000800026Q000600036Q000500086Q000400073Q00044Q001B00012Q0018010700014Q0018010600024Q0018010500073Q00201001073Q00052Q0001000700073Q0020A80007000700060026470007001A0001000700049F012Q001A0001001291000700033Q00060B0104001B0001000700049F012Q001B0001001291000400044Q007000075Q0020100107000700082Q001801086Q0018010900043Q00060B010A00220001000500049F012Q00220001001291000A00094Q0018010B00064Q00560107000B4Q003500076Q0024012Q00017Q00023Q00030B3Q00412Q6447726F7570626F7803013Q006103073Q00207900033Q000100122Q000500026Q000600016Q000700026Q000300076Q00039Q0000017Q00023Q00030B3Q00412Q6447726F7570626F7803013Q006203073Q00207900033Q000100122Q000500026Q000600016Q000700026Q000300076Q00039Q0000017Q000D3Q0003063Q0057696E646F7703093Q0041637469766554616203063Q0069706169727303043Q0054616273030B3Q0053657453656C656374656403073Q00436F6C756D6E41030E3Q0043616E766173506F736974696F6E03073Q00566563746F72322Q033Q006E6577028Q0003073Q00436F6C756D6E42030A3Q005461624368616E67656403043Q0046697265012B3Q0020102Q013Q00010020102Q010001000200066A2Q01000500013Q00049F012Q000500012Q00AA012Q00023Q0012202Q0100033Q00201001023Q00010020100102000200042Q005E00010002000300049F012Q001000010020110006000500050006400105000E00013Q00049F012Q000E00012Q001200086Q0065010800014Q004D0106000800010006770001000A0001000200049F012Q000A00010020102Q013Q0001001056000100023Q0020102Q013Q00010020102Q0100010006001220010200083Q0020100102000200090012910003000A3Q0012910004000A4Q008C0102000400020010560001000700020020102Q013Q00010020102Q010001000B001220010200083Q0020100102000200090012910003000A3Q0012910004000A4Q008C0102000400020010560001000700020020102Q013Q00010020102Q010001000C00201100010001000D2Q001801036Q004D2Q01000300012Q00AA012Q00024Q0024012Q00017Q00043Q0003083Q0053656C656374656403063Q0069706169727303053Q00426F786573030A3Q0053657456697369626C6502133Q0006930001000500013Q00049F012Q000500012Q0065010200013Q0006FC000200060001000100049F012Q000600012Q006501025Q0010563Q000100022Q007000026Q005E010200010001001220010200023Q00201001033Q00032Q005E00020002000400049F012Q0010000100201100070006000400201001093Q00012Q004D0107000900010006770002000D0001000200049F012Q000D00012Q0024012Q00017Q00144Q0003053Q00436F756E7403073Q0056697369626C65010003043Q0054657874034Q0003063Q0042752Q746F6E03063Q004163746976652Q0103053Q0054772Q656E03053Q004C6162656C03103Q00546578745472616E73706172656E6379028Q00030A3Q0054657874436F6C6F723303083Q0053656C65637465642Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403093Q00636F6C6F722E6D696403083Q00746F737472696E6702CD5QCCE43F023A3Q0026470001001D0001000100049F012Q001D000100201001023Q000200300500020003000400201001023Q000200300500020005000600201001023Q00070030050002000800092Q007000025Q00201001020002000A00201001033Q000B2Q002A01043Q00020030050004000C000D00201001053Q000F0006930005001600013Q00049F012Q001600012Q0070000500013Q002010010500050010001291000600114Q00890005000200020006FC0005001A0001000100049F012Q001A00012Q0070000500013Q002010010500050010001291000600124Q00890005000200020010560004000E00052Q004D0102000400012Q0024012Q00013Q00201001023Q0002000E0F000D00210001000100049F012Q002100012Q001200036Q0065010300013Q00105600020003000300201001023Q0002000EC8000D002B0001000100049F012Q002B0001001220010300134Q0018010400014Q00890003000200020006FC0003002C0001000100049F012Q002C0001001291000300063Q0010560002000500032Q000C00025Q00202Q00020002000A00202Q00033Q000B4Q00043Q000100262Q000100360001000D00049F012Q00360001001291000500143Q0006FC000500370001000100049F012Q003700010012910005000D3Q0010560004000C00052Q004D0102000400012Q0024012Q00017Q00073Q0003063Q0069706169727303053Q00426F78657303073Q0044657374726F7903043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C01113Q0012202Q0100013Q00201001023Q00022Q005E00010002000300049F012Q000600010020110006000500032Q0004010600020001000677000100040001000200049F012Q000400012Q002A2Q015Q0010563Q000200010020102Q013Q000400208B2Q01000100054Q00010002000100202Q00013Q000600202Q0001000100074Q0001000200016Q00017Q00233Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C03093Q00636F72652F4D61696403113Q00636F6D706F6E656E74732F546F2Q676C6503113Q00636F6D706F6E656E74732F536C6964657203133Q00636F6D706F6E656E74732F44726F70646F776E03143Q00636F6D706F6E656E74732F4B65795069636B657203163Q00636F6D706F6E656E74732F436F6C6F725069636B657203113Q00636F6D706F6E656E74732F42752Q746F6E03103Q00636F6D706F6E656E74732F496E70757403103Q00636F6D706F6E656E74732F4C6162656C03123Q00636F6D706F6E656E74732F4469766964657203073Q002Q5F696E646578026Q002240026Q00204003093Q006E6F726D616C6973652Q033Q006E6577030D3Q00436F6E74656E7448656967687403073Q0052656672657368030C3Q00536574436F2Q6C6170736564030A3Q0053657456697369626C6503063Q00412Q64526F7703093Q00412Q64546F2Q676C6503093Q00412Q64536C69646572030B3Q00412Q6444726F70646F776E030C3Q00412Q644B65795069636B6572030E3Q00412Q64436F6C6F725069636B657203093Q00412Q6442752Q746F6E030C3Q00412Q6442752Q746F6E526F7703083Q00412Q64496E70757403083Q00412Q644C6162656C030A3Q00412Q644469766964657203073Q0044657374726F7901764Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q00890004000200022Q001801055Q001291000600054Q00890005000200022Q001801065Q001291000700064Q00890006000200022Q001801075Q001291000800074Q00890007000200022Q006500085Q00122Q000900086Q0008000200024Q00095Q00122Q000A00096Q0009000200024Q000A5Q00122Q000B000A6Q000A000200024Q000B5Q00122Q000C000B6Q000B000200024Q000C5Q00122Q000D000C6Q000C000200024Q000D5Q00122Q000E000D6Q000D000200024Q000E5Q00122Q000F000E6Q000E000200024Q000F5Q00102Q000F000F000F001291001000103Q001291001100113Q00029001125Q001056000F001200120006D400130001000100082Q0018012Q000F4Q0018012Q00054Q0018012Q00044Q0018012Q00014Q0018012Q00024Q0018012Q00104Q0018012Q00114Q0018012Q00033Q001056000F00130013000290011300023Q001056000F001400130006D400130003000100012Q0018012Q00103Q001056000F001500130006D400130004000100022Q0018012Q00104Q0018012Q00033Q001056000F00160013000290011300053Q001056000F001700130006D400130006000100052Q0018012Q00024Q0018012Q00014Q0018012Q00054Q0018017Q0018012Q00033Q001056000F001800130006D400130007000100022Q0018012Q00124Q0018012Q00063Q001056000F001900130006D400130008000100022Q0018012Q00124Q0018012Q00073Q001056000F001A00130006D400130009000100022Q0018012Q00124Q0018012Q00083Q001056000F001B00130006D40013000A000100022Q0018012Q00124Q0018012Q00093Q001056000F001C00130006D40013000B000100022Q0018012Q00124Q0018012Q000A3Q001056000F001D00130006D40013000C000100022Q0018012Q00124Q0018012Q000B3Q001056000F001E00130006D40013000D000100012Q0018012Q000B3Q001056000F001F00130006D40013000E000100022Q0018012Q00124Q0018012Q000C3Q001056000F002000130006D40013000F000100022Q0018012Q00124Q0018012Q000D3Q001056000F002100130006D400130010000100012Q0018012Q000E3Q001056000F00220013000290011300113Q001056000F002300132Q00AA010F00024Q0024012Q00013Q00123Q00023Q0003043Q007479706503053Q007461626C65020E3Q001220010200014Q001801036Q0089000200020002002647000200080001000200049F012Q000800012Q001E000200024Q001801036Q00B6000200034Q001801025Q00060B0103000C0001000100049F012Q000C00012Q002A01036Q00B6000200034Q0024012Q00017Q00593Q00030C3Q007365746D6574617461626C652Q033Q0054616203063Q0057696E646F7703053Q005469746C6503043Q005369646503043Q00526F777303093Q00436F2Q6C6170736564010003043Q004D6169642Q033Q006E657703073Q00526573697A656403013Q006203073Q00436F6C756D6E4203073Q00436F6C756D6E4103043Q00522Q6F742Q033Q004E657703053Q004672616D6503043Q004E616D6503093Q0047726F7570626F785F03043Q0053697A6503053Q005544696D32026Q00F03F028Q00026Q003E4003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030B3Q00616C7068612E70616E656C030B3Q004C61796F75744F7264657203093Q004E6578744F7264657203073Q0056697369626C6503063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E626F7803063Q005374726F6B65030A3Q00616C7068612E6C696E6503043Q004769766503043Q00426F647903083Q00506F736974696F6E030A3Q0066726F6D4F2Q66736574027Q004003063Q004C61796F7574030C3Q0055494C6973744C61796F757403073Q0050612Q64696E6703043Q005544696D03093Q00536F72744F7264657203043Q00456E756D030B3Q005469746C65486F6C646572026Q0018C0026Q002440026Q002840030D3Q004175746F6D6174696353697A6503013Q0058030A3Q00636F6C6F722E6D61736B03063Q005A496E646578026Q000840026Q001440030D3Q0046692Q6C446972656374696F6E030A3Q00486F72697A6F6E74616C03113Q00566572746963616C416C69676E6D656E7403063Q0043656E746572026Q00104003093Q005469746C655465787403043Q0054657874030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903053Q007469746C6503073Q0043686576726F6E03013Q002D03083Q00636F6C6F722E6C6F026Q001C40030E3Q005465787458416C69676E6D656E74030B3Q00436F2Q6C61707369626C6503053Q00736D612Q6C030B3Q005469746C6542752Q746F6E030A3Q005465787442752Q746F6E2Q033Q0048697403093Q0066726F6D5363616C65034Q0003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374030A3Q004D6F757365456E746572030A3Q004D6F7573654C6561766503183Q0047657450726F70657274794368616E6765645369676E616C03133Q004162736F6C757465436F6E74656E7453697A65030C3Q00536574436F2Q6C6170736564030B3Q005265676973746572426F78044B012Q0006FC000300040001000100049F012Q000400012Q002A01046Q0018010300043Q001220010400014Q002A01056Q007000066Q008C010400060002001056000400023Q00201001053Q00030010560004000300050010560004000400020010560004000500012Q002A01055Q0010560004000600050030050004000700082Q0070000500013Q00201001050005000A2Q00F20005000100020010560004000900052Q0070000500023Q00201001050005000A2Q00F20005000100020010560004000B00050026470001001E0001000C00049F012Q001E000100201001053Q000300201001050005000D0006FC000500200001000100049F012Q0020000100201001053Q000300201001050005000E2Q0070000600033Q00208400060006001000122Q000700116Q00083Q000700122Q000900136Q000A00026Q00090009000A00102Q00080012000900122Q000900153Q00202Q00090009000A00122Q000A00163Q00122Q000B00173Q00122Q000C00173Q00122Q000D00186Q0009000D000200102Q0008001400094Q000900033Q00202Q00090009001A00122Q000A001B6Q00090002000200102Q0008001900094Q000900033Q00202Q00090009001A00122Q000A001D6Q00090002000200102Q0008001C000900202Q00093Q000300202Q00090009001F4Q00090002000200102Q0008001E000900302Q00080020000800102Q0008002100054Q00060008000200102Q0004000F00064Q000600033Q00202Q0006000600224Q000700043Q00202Q00070007002300122Q000800246Q00070002000200202Q00080004000F4Q0006000800014Q000600033Q00202Q00060006002500202Q00070004000F00122Q0008001B3Q00122Q000900266Q00060009000100202Q00060004000900202Q00060006002700202Q00080004000F4Q0006000800014Q000600033Q00202Q00060006001000122Q000700116Q00083Q000500302Q00080012002800122Q000900153Q00202Q00090009002A4Q000A00056Q000B00056Q0009000B000200102Q00080029000900122Q000900153Q00202Q00090009000A00122Q000A00166Q000B00056Q000B000B3Q00202Q000B000B002B00122Q000C00166Q000D00056Q000D000D3Q00202Q000D000D002B4Q0009000D000200102Q00080014000900302Q0008001C001600202Q00090004000F00102Q0008002100094Q00060008000200102Q0004002800064Q000600033Q0020100106000600100012F00007002D6Q00083Q000300122Q0009002F3Q00202Q00090009000A00122Q000A00173Q00122Q000B00176Q0009000B000200102Q0008002E000900122Q000900313Q00202Q00090009003000202Q00090009001E00102Q00080030000900202Q00090004002800102Q0008002100094Q00060008000200102Q0004002C00064Q000600033Q00202Q00060006001000122Q000700116Q00083Q000800302Q00080012000400122Q000900153Q00202Q00090009000A00122Q000A00176Q000B00063Q00122Q000C00173Q00122Q000D00336Q0009000D000200102Q00080029000900122Q000900153Q00202Q00090009002A00122Q000A00343Q00122Q000B00356Q0009000B000200102Q00080014000900122Q000900313Q00202Q00090009003600202Q00090009003700102Q0008003600094Q000900033Q00202Q00090009001A00122Q000A00386Q00090002000200102Q00080019000900302Q0008001C001700302Q00080039003A00202Q00090004000F00102Q0008002100094Q00060008000200102Q0004003200064Q000600033Q00202Q00060006002E00202Q00070004003200122Q000800173Q00122Q0009003B3Q00122Q000A00173Q00122Q000B003B6Q0006000B00014Q000600033Q00202Q00060006001000122Q0007002D6Q00083Q000500122Q000900313Q00202Q00090009003C00202Q00090009003D00102Q0008003C000900122Q000900313Q00202Q00090009003E00202Q00090009003F00102Q0008003E000900122Q0009002F3Q00202Q00090009000A00122Q000A00173Q00122Q000B00406Q0009000B000200102Q0008002E000900122Q000900313Q00202Q00090009003000202Q00090009001E00102Q0008003000090020100109000400320010560008002100092Q004D0106000800012Q0070000600033Q0020100106000600422Q002A01073Q00080030050007001200420010560007004200022Q0070000800033Q00201001080008001A001291000900444Q00F700080002000200102Q00070043000800122Q000800153Q00202Q00080008002A00122Q000900173Q00122Q000A00356Q0008000A000200102Q00070014000800122Q000800313Q00202Q00080008003600201001080008003700102201070036000800302Q0007001E001600302Q00070039004000202Q00080004003200102Q00070021000800122Q000800456Q00060008000200102Q0004004100064Q000600033Q00202Q0006000600422Q002A01073Q000900301C01070012004600302Q0007004200474Q000800033Q00202Q00080008001A00122Q000900486Q00080002000200102Q00070043000800122Q000800153Q00202Q00080008002A00122Q000900493Q001291000A00354Q008C0108000A0002001056000700140008001220010800313Q00201001080008004A00201001080008003F0010560007004A00080030050007001E002B00300500070039004000201001080003004B002647000800FA0001000800049F012Q00FA00012Q001200086Q0065010800013Q0010560007002000080020100108000400320010560007002100080012F80008004C6Q00060008000200102Q0004004600064Q000600033Q00202Q00060006001000122Q0007004E6Q00083Q000600302Q00080012004F00122Q000900153Q00202Q000900090050001291000A00163Q001291000B00164Q008C0109000B00020010560008001400090030050008001C001600300500080042005100300500080039003B0020100109000400320010560008002100092Q008C0106000800020010560004004D000600201001060003004B002696000600342Q01000800049F012Q00342Q0100201001060004000900201100060006002700201001080004004D0020100108000800520020110008000800530006D4000A3Q000100012Q0018012Q00044Q003C0108000A6Q00063Q000100202Q00060004000900202Q00060006002700202Q00080004004D00202Q00080008005400202Q0008000800530006D4000A0001000100022Q00703Q00074Q0018012Q00044Q003C0108000A6Q00063Q000100202Q00060004000900202Q00060006002700202Q00080004004D00202Q00080008005500202Q0008000800530006D4000A0002000100032Q00703Q00074Q0018012Q00044Q00703Q00044Q00720108000A4Q006101063Q000100201001060004000900206300060006002700202Q00080004002C00202Q00080008005600122Q000A00576Q0008000A000200202Q0008000800530006D4000A0003000100012Q0018012Q00044Q00720108000A4Q006101063Q0001002010010600030007000693000600462Q013Q00049F012Q00462Q010020110006000400582Q0065010800014Q0065010900014Q004D01060009000100201100063Q00592Q0018010800044Q004D0106000800012Q00AA010400024Q0024012Q00013Q00043Q00023Q00030C3Q00536574436F2Q6C617073656403093Q00436F2Q6C617073656400074Q00707Q002079014Q00014Q00025Q00202Q0002000200024Q000200028Q000200016Q00017Q00063Q0003053Q0054772Q656E03093Q005469746C6554657874030A3Q0054657874436F6C6F723303063Q00436F6C6F72332Q033Q006E6577026Q00F03F000E4Q00707Q002010014Q00012Q0070000100013Q0020102Q01000100022Q002A01023Q0001001220010300043Q00204300030003000500122Q000400063Q00122Q000500063Q00122Q000600066Q0003000600020010560002000300032Q004D012Q000200012Q0024012Q00017Q00053Q0003053Q0054772Q656E03093Q005469746C6554657874030A3Q0054657874436F6C6F72332Q033Q0047657403083Q00636F6C6F722E6869000C4Q0035016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q00014Q000300023Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200016Q00017Q00013Q0003073Q005265667265736800044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00083Q00028Q0003063Q0069706169727303043Q00526F777303043Q00522Q6F7403073Q0056697369626C6503043Q0053697A6503013Q005903063Q004F2Q6673657401123Q001291000100013Q001220010200023Q00201001033Q00032Q005E00020002000400049F012Q000E00010020100107000600040020100107000700050006930007000E00013Q00049F012Q000E00010020100107000600040020100107000700060020100107000700070020100107000700082Q009E2Q0100010007000677000200050001000200049F012Q000500012Q00AA2Q0100024Q0024012Q00017Q000C3Q0003093Q00436F2Q6C617073656403043Q00522Q6F7403043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q002C40030D3Q00436F6E74656E74486569676874027Q004003073Q00526573697A656403043Q004669726501213Q0020102Q013Q00010006930001000D00013Q00049F012Q000D00010020102Q013Q0002001283000200043Q00202Q00020002000500122Q000300063Q00122Q000400073Q00122Q000500073Q00122Q000600086Q00020006000200102Q0001000300026Q00013Q00201100013Q00092Q00890001000200020026EC000100120001000700049F012Q001200010012910001000A3Q00201001023Q00020012D9000300043Q00202Q00030003000500122Q000400063Q00122Q000500073Q00122Q000600076Q00075Q00202Q00070007000A4Q0007000100074Q00030007000200102Q00020003000300201001023Q000B00201100020002000C2Q00040102000200012Q0024012Q00017Q00123Q0003093Q00436F2Q6C617073656403043Q00426F647903073Q0056697369626C6503073Q0043686576726F6E03043Q005465787403013Q002B03013Q002D03073Q0052656672657368026Q002C40030D3Q00436F6E74656E74486569676874027Q004003053Q0054772Q656E03043Q00522Q6F7403043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q0003323Q0006930001000500013Q00049F012Q000500012Q0065010300013Q0006FC000300060001000100049F012Q000600012Q006501035Q0010563Q0001000300206A00033Q000200202Q00043Q00014Q000400043Q00102Q00030003000400202Q00033Q000400202Q00043Q000100062Q0004001200013Q00049F012Q00120001001291000400063Q0006FC000400130001000100049F012Q00130001001291000400073Q0010560003000500040006930002001900013Q00049F012Q0019000100201100033Q00082Q000401030002000100049F012Q0031000100201001033Q00010006930003001F00013Q00049F012Q001F0001001291000300093Q0006FC000300240001000100049F012Q0024000100201100033Q000A2Q00890003000200022Q007000045Q00201F01040004000B2Q009E0103000300042Q0070000400013Q00201001040004000C00201001053Q000D2Q002A01063Q00010012200107000F3Q002010010700070010001291000800113Q001291000900123Q001291000A00124Q0018010B00034Q008C0107000B00020010560006000E00072Q004D0104000600012Q0024012Q00017Q00023Q0003043Q00522Q6F7403073Q0056697369626C6502093Q00201001023Q00010006930001000600013Q00049F012Q000600012Q0065010300013Q0006FC000300070001000100049F012Q000700012Q006501035Q0010560002000200032Q0024012Q00017Q005F3Q0003063Q004865696768742Q033Q0047657403083Q0073697A652E726F77030D3Q0073697A652E636865636B626F78026Q001C402Q033Q004E657703053Q004672616D6503043Q004E616D652Q033Q00526F7703043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q0003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030B3Q004C61796F75744F7264657203043Q00526F777303063Q00506172656E7403043Q00426F647903063Q00436F726E6572026Q00084003043Q00522Q6F7403083Q0047726F7570626F7803043Q004D61696403083Q0044697361626C6564010003043Q0054657874034Q0003043Q004769766503083Q00436865636B626F78030A3Q005465787442752Q746F6E03053Q00436865636B030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F03083Q00506F736974696F6E030A3Q0066726F6D4F2Q6673657403073Q0056697369626C652Q01025Q00388F40030B3Q00436865636B5374726F6B6503083Q0055495374726F6B6503053Q00436F6C6F7203083Q00636F6C6F722E6C6F03093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203043Q00536C6F74030D3Q004175746F6D6174696353697A6503013Q005803063Q005A496E646578027Q0040030C3Q0055494C6973744C61796F7574030D3Q0046692Q6C446972656374696F6E030A3Q00486F72697A6F6E74616C03133Q00486F72697A6F6E74616C416C69676E6D656E7403053Q00526967687403113Q00566572746963616C416C69676E6D656E7403063Q0043656E74657203073Q0050612Q64696E6703043Q005544696D026Q00104003093Q00536F72744F7264657203053Q004C6162656C030A3Q0054657874436F6C6F723303093Q00636F6C6F722E6D6964030C3Q00546578745472756E6361746503053Q004174456E6403183Q0047657450726F70657274794368616E6765645369676E616C030C3Q004162736F6C75746553697A6503073Q00436F2Q6E65637403073Q00542Q6F6C74697003083Q005175657374696F6E03043Q0048696E7403013Q003F026Q002440030E3Q005465787458416C69676E6D656E7403053Q00736D612Q6C030B3Q00542Q6F6C7469705465787403103Q006F7665726C6179732F542Q6F6C74697003063Q00412Q74616368030A3Q004D6F757365456E746572030A3Q004D6F7573654C656176652Q033Q0048697403093Q0066726F6D5363616C65030B3Q0053657444697361626C656403093Q00536574416374697665030A3Q0053657456697369626C6503073Q005265667265736803063Q0057696E646F7703083Q00496E646578526F770284012Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q0020100102000100010006FC0002000B0001000100049F012Q000B00012Q007000025Q002010010200020002001291000300034Q00890002000200022Q007000035Q002010010300030002001291000400044Q00890003000200020020600004000300052Q0070000500013Q002010010500050006001291000600074Q002A01073Q00060030050007000800090012200108000B3Q00201001080008000C0012FE0009000D3Q00122Q000A000E3Q00122Q000B000E6Q000C00026Q0008000C000200102Q0007000A00084Q000800013Q00202Q00080008001000122Q000900116Q0008000200020010560007000F000800300500070012000D00201001083Q00142Q0001000800083Q00206000080008000D00105600070013000800201001083Q00160010560007001500082Q008C0105000700022Q0070000600013Q002010010600060017001291000700184Q0018010800054Q004D0106000800012Q002A01063Q00050010560006001900050010560006001A4Q0070000700023Q00201001070007000C2Q00F20007000100020010560006001B00070030050006001C001D00201001070001001E0006FC0007003B0001000100049F012Q003B00010012910007001F3Q0010560006001E000700203300070006001B00202Q0007000700204Q000900056Q0007000900014Q000700013Q0020ED00070007000600122Q000800226Q00093Q000800302Q00090008002300122Q000A00253Q00202Q000A000A000C00122Q000B000E3Q00122Q000C00266Q000A000C000200102Q00090024000A001220010A000B3Q002010010A000A000C001291000B000E3Q001291000C000E3Q001291000D00263Q001291000E000E4Q008C010A000E000200105600090027000A001220010A000B3Q002010010A000A00282Q0018010B00034Q0018010C00034Q008C010A000C00020010560009000A000A00300500090012000D0030050009001E001F002010010A00010021002696000A005F0001002A00049F012Q005F00012Q0012000A6Q0065010A00013Q0010AF00090029000A00102Q0009001500054Q00070009000200102Q0006002100074Q000700013Q00202Q00070007001700122Q0008002B3Q00202Q0009000600214Q0007000900014Q000700013Q00202Q00070007000600122Q0008002D6Q00093Q00044Q000A5Q00202Q000A000A000200122Q000B002F6Q000A0002000200102Q0009002E000A00302Q00090030000D00122Q000A00323Q00202Q000A000A003100202Q000A000A003300102Q00090031000A00202Q000A0006002100102Q00090015000A4Q00070009000200102Q0006002C00074Q000700013Q00202Q00070007000600122Q000800076Q00093Q000800302Q00090008003400122Q000A00253Q00202Q000A000A000C00122Q000B000D3Q00122Q000C00266Q000A000C000200102Q00090024000A00122Q000A000B3Q00202Q000A000A000C00122Q000B000D3Q00122Q000C000E3Q00122Q000D00263Q00122Q000E000E6Q000A000E000200102Q00090027000A00122Q000A000B3Q00202Q000A000A000C00122Q000B000E3Q00122Q000C000E3Q00122Q000D000D3Q00122Q000E000E6Q000A000E000200102Q0009000A000A00122Q000A00323Q00202Q000A000A003500202Q000A000A003600102Q00090035000A00302Q00090012000D00302Q00090037003800102Q0009001500054Q00070009000200102Q0006003400074Q000700013Q00202Q00070007000600122Q000800396Q00093Q000600122Q000A00323Q00202Q000A000A003A00202Q000A000A003B00102Q0009003A000A00122Q000A00323Q00202Q000A000A003C00202Q000A000A003D00102Q0009003C000A00122Q000A00323Q00202Q000A000A003E00202Q000A000A003F00102Q0009003E000A00122Q000A00413Q002010010A000A000C001291000B000E3Q001291000C00424Q008C010A000C000200105600090040000A001220010A00323Q002010010A000A0043002010010A000A001300105600090043000A002010010A0006003400105600090015000A2Q004D01070009000100201001070001001E000693000700EB00013Q00049F012Q00EB00012Q0070000700013Q00203B01070007001E4Q00083Q000700302Q00080008004400202Q00090001001E00102Q0008001E00094Q000900013Q00202Q00090009001000122Q000A00466Q00090002000200102Q0008004500090012200109000B3Q0020100109000900282Q0018010A00043Q001291000B000E4Q008C0109000B00020010560008002700090012200109000B3Q00201001090009000C001291000A000D4Q0085010B00043Q001291000C000D3Q001291000D000E4Q008C0109000D00020010560008000A0009001220010900323Q0020100109000900470020100109000900480010560008004700090010560008001500052Q008900070002000200109F00060044000700202Q00070006001B00202Q00070007002000202Q00090006003400202Q000900090049001291000B004A4Q008C0109000B000200201100090009004B0006D4000B3Q000100022Q0018012Q00064Q0018012Q00044Q00720109000B4Q006101073Q000100201001070001004C0006930007003B2Q013Q00049F012Q003B2Q012Q0070000700013Q00204100070007001E4Q00083Q000800302Q00080008004E00302Q0008001E004F4Q000900013Q00202Q00090009001000122Q000A002F6Q00090002000200102Q00080045000900122Q0009000B3Q002010010900090028001291000A00504Q0018010B00024Q008C0109000B00020010560008000A0009001220010900323Q00201001090009005100201001090009003F00105600080051000900300500080012000D003005000800370018001056000800150005001291000900523Q001291000A00224Q008C0107000A00020010560006004D000700201001070006004D0012200108000B3Q0020100108000800282Q0018010900043Q001291000A000E4Q008C0108000A000200105600070027000800201001070001004C0010560006005300072Q0070000700033Q001291000800544Q008900070002000200201001080007005500201001090006004D002010010A0001004C002010010B0006001B2Q004D0108000B000100200400080006001B00202Q00080008002000202Q000A0006004D00202Q000A000A005600202Q000A000A004B0006D4000C0001000100032Q00703Q00044Q0018012Q00064Q00708Q003C010A000C6Q00083Q000100202Q00080006001B00202Q00080008002000202Q000A0006004D00202Q000A000A005700202Q000A000A004B0006D4000C0002000100032Q00703Q00044Q0018012Q00064Q00708Q0083010A000C6Q00083Q000100202Q00080006001B00202Q00080008002000202Q000A0005004900122Q000C004A6Q000A000C000200202Q000A000A004B0006D4000C0003000100022Q0018012Q00064Q0018012Q00044Q0072010A000C4Q006101083Q00012Q0070000700013Q0020ED00070007000600122Q000800226Q00093Q000500302Q00090008005800122Q000A000B3Q00202Q000A000A005900122Q000B000D3Q00122Q000C000D6Q000A000C000200102Q0009000A000A00300500090012000D0030050009001E001F0010560009001500052Q008C01070009000200105600060058000700200400070006001B00202Q00070007002000202Q00090006005800202Q00090009005600202Q00090009004B0006D4000B0004000100042Q0018012Q00064Q00703Q00044Q0018012Q00054Q00708Q003C0109000B6Q00073Q000100202Q00070006001B00202Q00070007002000202Q00090006005800202Q00090009005700202Q00090009004B0006D4000B0005000100042Q00703Q00044Q0018012Q00054Q0018012Q00064Q00708Q00720109000B4Q006101073Q00010006D400070006000100012Q00707Q0010560006005A00070006D400070007000100012Q00707Q0010560006005B0007000290010700083Q0010560006005C000700201001073Q001400201001083Q00142Q0001000800083Q00206000080008000D2Q004A01070008000600201001073Q001B00201100070007002000201001090006001B2Q004D01070009000100201100073Q005D2Q000401070002000100201001073Q005E000693000700822Q013Q00049F012Q00822Q0100201001073Q005E00201001070007005F000693000700822Q013Q00049F012Q00822Q0100201001073Q005E00201100070007005F2Q0018010900064Q0018010A6Q004D0107000A00012Q00AA010600024Q0024012Q00013Q00093Q000A3Q0003043Q00536C6F74030C3Q004162736F6C75746553697A6503013Q005803053Q004C6162656C03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F026Q001840029Q00124Q00367Q00206Q000100206Q000200206Q00034Q00015Q00202Q00010001000400122Q000200063Q00202Q00020002000700122Q000300086Q000400014Q0085010400044Q001D000400043Q00202Q00040004000900122Q000500083Q00122Q0006000A6Q00020006000200102Q0001000500026Q00017Q00053Q0003053Q0054772Q656E03083Q005175657374696F6E030A3Q0054657874436F6C6F72332Q033Q00476574030C3Q00636F6C6F722E612Q63656E74000C4Q0035016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q00014Q000300023Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200016Q00017Q00053Q0003053Q0054772Q656E03083Q005175657374696F6E030A3Q0054657874436F6C6F72332Q033Q0047657403083Q00636F6C6F722E6C6F000C4Q0035016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q00014Q000300023Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200016Q00017Q000E3Q0003053Q004C6162656C030A3Q0054657874426F756E647303013Q0058028Q0003083Q005175657374696F6E03083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q6673657403043Q006D6174682Q033Q006D696E026Q0008402Q033Q006D6178030C3Q004162736F6C75746553697A65026Q00244000254Q00707Q002010014Q00010006FC3Q00050001000100049F012Q000500012Q0024012Q00014Q00707Q002010014Q0001002010014Q00020006933Q000D00013Q00049F012Q000D00010020102Q013Q00030006FC0001000E0001000100049F012Q000E0001001291000100044Q007000025Q002010010200020005001220010300073Q0020100103000300082Q0070000400013Q001220010500093Q00201001050005000A00206000060001000B001220010700093Q00201001070007000C001291000800044Q007000095Q00201001090009000100201001090009000D00201001090009000300203E00090009000E2Q0072010700094Q007301053Q00022Q009E010400040005001291000500044Q008C0103000500020010560002000600032Q0024012Q00017Q00083Q0003083Q0044697361626C656403053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030E3Q00616C7068612E726F77486F76657203053Q004C6162656C030A3Q0054657874436F6C6F723303083Q00636F6C6F722E6869001F4Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q00204C014Q00024Q000100026Q00023Q00014Q000300033Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200012Q00707Q002010014Q00060006933Q001E00013Q00049F012Q001E00012Q00703Q00013Q002010014Q00022Q007000015Q0020102Q01000100062Q002A01023Q00012Q0070000300033Q002010010300030004001291000400084Q00890003000200020010560002000700032Q004D012Q000200012Q0024012Q00017Q00083Q0003053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03053Q004C6162656C03063Q00416374697665030A3Q0054657874436F6C6F72332Q033Q0047657403093Q00636F6C6F722E6D6964001A4Q00387Q00206Q00014Q000100016Q00023Q000100302Q0002000200036Q000200016Q00023Q00206Q000400064Q001900013Q00049F012Q001900012Q00703Q00023Q002010014Q00050006FC3Q00190001000100049F012Q001900012Q00707Q002010014Q00012Q0070000100023Q0020102Q01000100042Q002A01023Q00012Q0070000300033Q002010010300030007001291000400084Q00890003000200020010560002000600032Q004D012Q000200012Q0024012Q00017Q00103Q0003083Q0044697361626C65642Q033Q0048697403063Q0041637469766503053Q004C6162656C030A3Q0054657874436F6C6F72332Q033Q0047657403083Q00636F6C6F722E6C6F03093Q00636F6C6F722E6D696403043Q00536C6F7403073Q0056697369626C652Q0103063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q004775694F626A65637403083Q00436865636B626F7802343Q0006930001000500013Q00049F012Q000500012Q0065010200013Q0006FC000200060001000100049F012Q000600012Q006501025Q0010563Q0001000200204600023Q000200202Q00033Q00014Q000300033Q00102Q00020003000300202Q00023Q000400062Q0002001D00013Q00049F012Q001D000100201001023Q000400201001033Q00010006930003001800013Q00049F012Q001800012Q007000035Q002010010300030006001291000400074Q00890003000200020006FC0003001C0001000100049F012Q001C00012Q007000035Q002010010300030006001291000400084Q008900030002000200105600020005000300201001023Q00090030050002000A000B0012200102000C3Q00201001033Q000900201100030003000D2Q00F6000300044Q00A401023Q000400049F012Q002D000100201100070006000E0012910009000F4Q008C0107000900020006930007002D00013Q00049F012Q002D000100201001073Q00012Q005F000700073Q001056000600030007000677000200250001000200049F012Q0025000100201001023Q001000201001033Q00012Q005F000300033Q0010560002000300032Q0024012Q00017Q00063Q0003063Q0041637469766503053Q004C6162656C030A3Q0054657874436F6C6F72332Q033Q0047657403083Q00636F6C6F722E686903093Q00636F6C6F722E6D6964021A3Q0006930001000500013Q00049F012Q000500012Q0065010200013Q0006FC000200060001000100049F012Q000600012Q006501025Q0010563Q0001000200201001023Q00020006930002001900013Q00049F012Q0019000100201001023Q000200201001033Q00010006930003001400013Q00049F012Q001400012Q007000035Q002010010300030004001291000400054Q00890003000200020006FC000300180001000100049F012Q001800012Q007000035Q002010010300030004001291000400064Q00890003000200020010560002000300032Q0024012Q00017Q00043Q0003043Q00522Q6F7403073Q0056697369626C6503083Q0047726F7570626F7803073Q0052656672657368020C3Q00201001023Q00010006930001000600013Q00049F012Q000600012Q0065010300013Q0006FC000300070001000100049F012Q000700012Q006501035Q00105600020002000300201001023Q00030020110002000200042Q00040102000200012Q0024012Q00017Q00013Q002Q033Q006E6577030C4Q007B00038Q000400016Q000500026Q0003000500044Q000500013Q00202Q0005000500014Q00068Q000700036Q000800046Q000500086Q00059Q0000017Q00013Q002Q033Q006E6577030C4Q007B00038Q000400016Q000500026Q0003000500044Q000500013Q00202Q0005000500014Q00068Q000700036Q000800046Q000500086Q00059Q0000017Q00013Q002Q033Q006E6577030C4Q007B00038Q000400016Q000500026Q0003000500044Q000500013Q00202Q0005000500014Q00068Q000700036Q000800046Q000500086Q00059Q0000017Q00013Q002Q033Q006E6577030C4Q007B00038Q000400016Q000500026Q0003000500044Q000500013Q00202Q0005000500014Q00068Q000700036Q000800046Q000500086Q00059Q0000017Q00013Q002Q033Q006E6577030C4Q007B00038Q000400016Q000500026Q0003000500044Q000500013Q00202Q0005000500014Q00068Q000700036Q000800046Q000500086Q00059Q0000017Q00013Q002Q033Q006E6577030B4Q007000036Q0018010400014Q0018010500024Q00270003000500042Q002F010500013Q00202Q0005000500014Q00068Q000700046Q000500076Q00059Q0000017Q00013Q002Q033Q00726F7702074Q002F01025Q00202Q0002000200014Q00038Q000400016Q000200046Q00029Q0000017Q00013Q002Q033Q006E6577030C4Q007B00038Q000400016Q000500026Q0003000500044Q000500013Q00202Q0005000500014Q00068Q000700036Q000800046Q000500086Q00059Q0000017Q00053Q0003043Q007479706503063Q00737472696E670003043Q00546578742Q033Q006E657703154Q007000036Q0018010400014Q0018010500024Q0027000300050004001220010500014Q0018010600014Q00890005000200020026470005000E0001000200049F012Q000E00010026470002000E0001000300049F012Q000E00012Q002A01053Q00010010560005000400012Q0018010400054Q0070000500013Q0020840105000500054Q00068Q000700046Q000500076Q00059Q0000017Q00013Q002Q033Q006E657701064Q00DD00015Q00202Q0001000100014Q00028Q000100026Q00019Q0000017Q00053Q0003043Q004D616964030A3Q00446F436C65616E696E6703043Q00526F777303073Q00526573697A6564030D3Q00446973636F2Q6E656374412Q6C01093Q0020102Q013Q00010020110001000100022Q00042Q01000200012Q002A2Q015Q0010563Q000300010020102Q013Q00040020110001000100052Q00042Q01000200012Q0024012Q00017Q00073Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C030A3Q00636F72652F466C61677303073Q002Q5F696E6465782Q033Q006E6577011B4Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q00890004000200022Q001801055Q001291000600054Q00890005000200022Q002A01065Q0010560006000600060006D400073Q000100062Q0018012Q00064Q0018012Q00044Q0018012Q00024Q0018012Q00034Q0018012Q00054Q0018016Q0010560006000700072Q00AA010600024Q0024012Q00013Q00013Q00273Q00030C3Q007365746D6574617461626C6503043Q005479706503063Q00546F2Q676C6503053Q0056616C756503073Q0044656661756C742Q0103083Q0043612Q6C6261636B03073Q004368616E6765642Q033Q006E657703083Q0047726F7570626F7803053Q005269736B7903063Q00412Q64526F7703043Q005465787403053Q005469746C6503063Q00746F2Q676C6503073Q00542Q6F6C74697003083Q00436865636B626F782Q033Q00526F7703073Q00456C656D656E7403063Q005374726F6B65030B3Q00436865636B5374726F6B6503063Q005F7061696E7403093Q005468656D65436F2Q6E03073Q00436F2Q6E65637403043Q004D61696403043Q004769766503083Q0053657456616C75652Q033Q0053657403083Q0047657456616C756503093Q004F6E4368616E676564030B3Q0053657444697361626C656403073Q00536574546578742Q033Q0048697403113Q004D6F75736542752Q746F6E31436C69636B030C3Q00412Q644B65795069636B6572030E3Q00412Q64436F6C6F725069636B657203073Q0044657374726F7903083Q0044697361626C656403083Q00526567697374657203883Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q005301048Q00058Q00030005000200302Q00030002000300202Q00040002000500262Q0004000D0001000600049F012Q000D00012Q001200046Q0065010400013Q0010560003000400040020100104000200070010560003000700042Q0070000400013Q0020100104000400092Q00F20004000100020010560003000800040010560003000A3Q00201001040002000B0010560003000B000400201100043Q000C2Q002A01063Q000300201001070002000D0006FC000700210001000100049F012Q0021000100201001070002000E0006FC000700210001000100049F012Q002100010012910007000F3Q0010560006000D00070020100107000200100010560006001000070030050006001100062Q008C01040006000200105600030012000400102301040013000300202Q00050004001100102Q00030011000500202Q00050004001500102Q0003001400050006D400053Q000100042Q0018012Q00034Q00703Q00024Q00703Q00034Q0018012Q00043Q0010560003001600052Q0070000600023Q0020100106000600080006930006003C00013Q00049F012Q003C00012Q0070000600023Q0020100106000600080020110006000600180006D400080001000100012Q0018012Q00054Q008C0106000800020010560003001700060020100106000300170006930006004400013Q00049F012Q0044000100201001060004001900201100060006001A0020100108000300172Q004D0106000800010006D400060002000100022Q0018012Q00054Q00703Q00043Q0010560003001B000600201001060003001B0010560003001C0006000290010600033Q0010560003001D00060006D400060004000100012Q0018012Q00043Q0010560003001E00060006D400060005000100012Q0018012Q00043Q0010560003001F00060006D400060006000100012Q0018012Q00043Q00105600030020000600200400060004001900202Q00060006001A00202Q00080004002100202Q00080008002200202Q0008000800180006D4000A0007000100022Q0018012Q00044Q0018012Q00034Q003C0108000A6Q00063Q000100202Q00060004001900202Q00060006001A00202Q00080003001100202Q00080008002200202Q0008000800180006D4000A0008000100022Q0018012Q00044Q0018012Q00034Q00720108000A4Q006101063Q00010006D400060009000100032Q00703Q00054Q0018012Q00044Q0018016Q0010560003002300060006D40006000A000100032Q00703Q00054Q0018012Q00044Q0018016Q0010560003002400060006D40006000B000100022Q0018012Q00044Q00703Q00043Q0010610003002500064Q000600056Q00078Q00060002000100202Q00060002002600062Q0006008000013Q00049F012Q0080000100201100060004001F2Q0065010800014Q004D0106000800012Q0070000600043Q00200200060006002700122Q0007000F6Q000800016Q000900036Q0006000900014Q000300028Q00013Q000C3Q000F3Q0003053Q0056616C75652Q033Q00476574030C3Q00636F6C6F722E612Q63656E74030B3Q00636F6C6F722E776869746503103Q004261636B67726F756E64436F6C6F723303163Q004261636B67726F756E645472616E73706172656E6379028Q00026Q00F03F03053Q0054772Q656E03083Q00436865636B626F7803063Q005374726F6B6503053Q00436F6C6F7203083Q00636F6C6F722E6C6F2Q033Q0053657403093Q00536574416374697665014D4Q007000015Q0020102Q01000100010006930001000A00013Q00049F012Q000A00012Q0070000200013Q002010010200020002001291000300034Q00890002000200020006FC0002000E0001000100049F012Q000E00012Q0070000200013Q002010010200020002001291000300044Q00890002000200022Q002A01033Q00020010560003000500020006930001001500013Q00049F012Q00150001001291000400073Q0006FC000400160001000100049F012Q00160001001291000400083Q0010560003000600040006933Q003300013Q00049F012Q003300012Q0070000400023Q00207C0004000400094Q00055Q00202Q00050005000A4Q000600036Q0004000600012Q0070000400023Q0020100104000400092Q007000055Q00201001050005000B2Q002A01063Q00010006930001002C00013Q00049F012Q002C00012Q0070000700013Q002010010700070002001291000800034Q00890007000200020006FC000700300001000100049F012Q003000012Q0070000700013Q0020100107000700020012910008000D4Q00890007000200020010560006000C00072Q004D01040006000100049F012Q004800012Q0070000400023Q00207C00040004000E4Q00055Q00202Q00050005000A4Q000600036Q0004000600012Q007000045Q00201001040004000B0006930001004300013Q00049F012Q004300012Q0070000500013Q002010010500050002001291000600034Q00890005000200020006FC000500470001000100049F012Q004700012Q0070000500013Q0020100105000500020012910006000D4Q00890005000200020010560004000C00052Q0070000400033Q00201100040004000F2Q0018010600014Q004D0104000600012Q0024012Q00019Q003Q00044Q00708Q00652Q016Q0004012Q000200012Q0024012Q00017Q00093Q0003053Q0056616C756503083Q0043612Q6C6261636B03053Q007063612Q6C03043Q007761726E03203Q005B4175726F72615D20746F2Q676C652063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q004368616E67656403043Q004669726503043Q00466C6167032B3Q0006930001000500013Q00049F012Q000500012Q0065010300013Q00060B2Q0100060001000300049F012Q000600012Q00652Q015Q00201001033Q000100066A2Q01000A0001000300049F012Q000A00012Q00AA012Q00023Q0010563Q000100012Q007000036Q0065010400014Q00040103000200010006FC000200290001000100049F012Q0029000100201001033Q00020006930003002000013Q00049F012Q00200001001220010300033Q00201001043Q00022Q0018010500014Q00270003000500040006FC000300200001000100049F012Q00200001001220010500043Q001280000600053Q00122Q000700066Q000800046Q0007000200024Q0006000600074Q00050002000100201001033Q00070020B10003000300084Q000500016Q0003000500014Q000300013Q00202Q00030003000800202Q00043Q00094Q000500016Q0003000500012Q00AA012Q00024Q0024012Q00017Q00013Q0003053Q0056616C756501033Q0020102Q013Q00012Q00AA2Q0100024Q0024012Q00017Q00053Q0003073Q004368616E67656403073Q00436F2Q6E65637403043Q004D61696403043Q004769766503053Q0056616C7565020E3Q00203701023Q000100202Q0002000200024Q000400016Q0002000400024Q00035Q00202Q00030003000300202Q0003000300044Q000500026Q0003000500014Q000300013Q00202Q00043Q00054Q0003000200016Q00028Q00017Q00013Q00030B3Q0053657444697361626C656402064Q000801025Q00202Q0002000200014Q000400016Q0002000400016Q00028Q00017Q00023Q0003053Q004C6162656C03043Q0054657874020B4Q007000025Q0020100102000200010006930002000700013Q00049F012Q000700012Q007000025Q0020100102000200010010560002000200012Q007000025Q0010560002000200012Q00AA012Q00024Q0024012Q00017Q00033Q0003083Q0044697361626C656403083Q0053657456616C756503053Q0056616C7565000C4Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002079014Q00024Q000200013Q00202Q0002000200034Q000200028Q000200016Q00017Q00033Q0003083Q0044697361626C656403083Q0053657456616C756503053Q0056616C7565000C4Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002079014Q00024Q000200013Q00202Q0002000200034Q000200028Q000200016Q00017Q00073Q0003143Q00636F6D706F6E656E74732F4B65795069636B657203133Q00636F6D706F6E656E74732F47726F7570626F7803093Q006E6F726D616C6973652Q033Q00526F7703043Q005465787403093Q004B65795069636B65722Q033Q006E6577031E4Q00A400035Q00122Q000400016Q0003000200024Q00045Q00122Q000500026Q00040002000200202Q0005000400034Q000600016Q000700026Q00050007000600062Q0006000E0001000100049F012Q000E00012Q002A01076Q0018010600074Q0070000700013Q0010560006000400070020100107000600050006FC000700150001000100049F012Q001500012Q0070000700013Q00201001070007000500105600060005000700204C0007000300074Q000800026Q000900056Q000A00066Q0007000A000200104Q000600076Q00028Q00017Q00063Q0003163Q00636F6D706F6E656E74732F436F6C6F725069636B657203133Q00636F6D706F6E656E74732F47726F7570626F7803093Q006E6F726D616C6973652Q033Q00526F77030B3Q00436F6C6F725069636B65722Q033Q006E657703184Q00A400035Q00122Q000400016Q0003000200024Q00045Q00122Q000500026Q00040002000200202Q0005000400034Q000600016Q000700026Q00050007000600062Q0006000E0001000100049F012Q000E00012Q002A01076Q0018010600074Q0070000700013Q00104101060004000700202Q0007000300064Q000800026Q000900056Q000A00066Q0007000A000200104Q000500076Q00028Q00017Q00063Q0003043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C030A3Q00556E726567697374657203043Q00466C6167010C4Q00BA00015Q00202Q00010001000100202Q0001000100024Q00010002000100202Q00013Q000300202Q0001000100044Q0001000200014Q000100013Q00202Q00010001000500202Q00023Q00062Q00042Q01000200012Q0024012Q00017Q000B3Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C030A3Q00636F72652F466C61677303093Q00636F72652F5574696C03043Q0067616D65030A3Q004765745365727669636503103Q0055736572496E7075745365727669636503073Q002Q5F696E6465782Q033Q006E657701244Q001700015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q00060002000200122Q000700073Q00202Q00070007000800122Q000900096Q0007000900024Q00085Q00102Q0008000A00080006D400093Q000100082Q0018012Q00084Q0018012Q00044Q0018012Q00024Q0018012Q00014Q0018012Q00064Q0018012Q00034Q0018012Q00054Q0018012Q00073Q0010560008000B00092Q00AA010800024Q0024012Q00013Q00013Q00593Q00030C3Q007365746D6574617461626C6503043Q005479706503063Q00536C696465722Q033Q004D696E028Q002Q033Q004D6178026Q00594003083Q00526F756E64696E6703063Q0053752Q666978034Q0003083Q0043612Q6C6261636B03073Q004368616E6765642Q033Q006E657703083Q0047726F7570626F7803063Q00412Q64526F7703043Q005465787403053Q005469746C6503063Q00736C6964657203073Q00542Q6F6C7469702Q033Q00526F7703073Q00456C656D656E7403053Q0057696474682Q033Q00476574030B3Q0073697A652E736C6964657203103Q0073697A652E736C69646572547261636B2Q033Q004E657703053Q004672616D6503043Q004E616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403083Q0073697A652E726F7703163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F030B3Q004C61796F75744F7264657203063Q00506172656E7403043Q00536C6F7403053Q00547261636B030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F03083Q00506F736974696F6E03103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E77652Q6C03063Q00436F726E6572025Q00388F4003043Q0046692Q6C030C3Q00636F6C6F722E612Q63656E7403043Q004B6E6F62026Q000840026Q00224003063Q005A496E646578027Q004003073Q00526561646F757403053Q0056616C756503013Q0030030A3Q0054657874436F6C6F723303083Q00636F6C6F722E6869030C3Q00526561646F75745769647468026Q004240030E3Q005465787458416C69676E6D656E7403043Q00456E756D03053Q00526967687403043Q006D6F6E6F2Q033Q00486974030A3Q005465787442752Q746F6E03053Q00636C616D7003073Q0044656661756C7403083Q0053657456616C75652Q033Q0053657403083Q0047657456616C756503083Q0053657452616E676503093Q004F6E4368616E676564030B3Q0053657444697361626C656403043Q004D61696403043Q0047697665030A3Q00496E707574426567616E03073Q00436F2Q6E656374030A3Q00496E707574456E646564030A3Q004D6F757365456E746572030A3Q004D6F7573654C6561766503043Q0053746570026Q00244003073Q0044657374726F7903083Q0044697361626C656403083Q00526567697374657203063Q006F7074696F6E0387012Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q002A01046Q007000056Q008C0103000500020030050003000200030020100104000200040006FC0004000D0001000100049F012Q000D0001001291000400053Q0010560003000400040020100104000200060006FC000400120001000100049F012Q00120001001291000400073Q0010560003000600040020100104000200080006FC000400170001000100049F012Q00170001001291000400053Q0010560003000800040020100104000200090006FC0004001C0001000100049F012Q001C00010012910004000A3Q00105600030009000400201001040002000B0010560003000B00042Q0070000400013Q00201001040004000D2Q00F20004000100020010560003000C00040010560003000E3Q00201100043Q000F2Q002A01063Q00020020100107000200100006FC0007002D0001000100049F012Q002D00010020100107000200110006FC0007002D0001000100049F012Q002D0001001291000700123Q00105600060010000700203E01070002001300102Q0006001300074Q00040006000200102Q00030014000400102Q00040015000300202Q00050002001600062Q0005003A0001000100049F012Q003A00012Q0070000500023Q002010010500050017001291000600184Q00890005000200022Q0070000600023Q0020A901060006001700122Q000700196Q0006000200024Q000700033Q00202Q00070007001A00122Q0008001B6Q00093Q000500302Q0009001C000300122Q000A001E3Q00202Q000A000A001F4Q000B00056Q000C00023Q00202Q000C000C001700122Q000D00206Q000C000D6Q000A3Q000200102Q0009001D000A00302Q00090021002200302Q00090023002200202Q000A0004002500102Q00090024000A4Q0007000900024Q000800033Q00202Q00080008001A00122Q0009001B6Q000A3Q000700302Q000A001C002600122Q000B00283Q00202Q000B000B000D00122Q000C00053Q00122Q000D00296Q000B000D000200102Q000A0027000B00122Q000B001E3Q00202Q000B000B000D00122Q000C00053Q00122Q000D00053Q00122Q000E00293Q00122Q000F00056Q000B000F000200102Q000A002A000B00122Q000B001E3Q00202Q000B000B000D00122Q000C00223Q00122Q000D00053Q00122Q000E00056Q000F00066Q000B000F000200102Q000A001D000B4Q000B00033Q00202Q000B000B002C00122Q000C002D6Q000B0002000200102Q000A002B000B4Q000B00033Q00202Q000B000B002C00122Q000C002E6Q000B0002000200102Q000A0021000B00102Q000A002400074Q0008000A000200102Q0003002600084Q000800033Q00202Q00080008002F00122Q000900303Q00202Q000A000300264Q0008000A00014Q000800033Q00202Q00080008001A00122Q0009001B6Q000A3Q000500302Q000A001C003100122Q000B001E3Q00202Q000B000B000D00122Q000C00053Q00122Q000D00053Q00122Q000E00223Q00122Q000F00056Q000B000F000200102Q000A001D000B2Q0070000B00033Q00206D000B000B002C00122Q000C00326Q000B0002000200102Q000A002B000B00302Q000A0021000500202Q000B0003002600102Q000A0024000B4Q0008000A000200102Q0003003100084Q000800033Q00202Q00080008002F00122Q000900303Q00202Q000A000300314Q0008000A00014Q000800033Q00202Q00080008001A00122Q0009001B6Q000A3Q000800302Q000A001C003300122Q000B00283Q00202Q000B000B000D00122Q000C00293Q00122Q000D00296Q000B000D000200102Q000A0027000B00122Q000B001E3Q00202Q000B000B000D00122Q000C00053Q00122Q000D00053Q00122Q000E00293Q00122Q000F00056Q000B000F000200102Q000A002A000B00122Q000B001E3Q00202Q000B000B001F00122Q000C00343Q00122Q000D00356Q000B000D000200102Q000A001D000B4Q000B00033Q00202Q000B000B002C00122Q000C00326Q000B0002000200102Q000A002B000B00302Q000A0021000500302Q000A0036003700202Q000B0003002600102Q000A0024000B4Q0008000A000200102Q0003003300084Q000800033Q00202Q00080008002F00122Q000900373Q00202Q000A000300334Q0008000A00014Q000800033Q00202Q0008000800104Q00093Q000700302Q0009001C003900302Q00090010003A4Q000A00033Q00202Q000A000A002C00122Q000B003C6Q000A0002000200102Q0009003B000A00122Q000A001E3Q00202Q000A000A001F00202Q000B0002003D00062Q000B00D30001000100049F012Q00D30001001291000B003E4Q0070000C00023Q0020AF010C000C001700122Q000D00206Q000C000D6Q000A3Q000200102Q0009001D000A00122Q000A00403Q00202Q000A000A003F00202Q000A000A004100102Q0009003F000A00302Q000900230037002010010A0004002500105600090024000A0012F8000A00426Q0008000A000200102Q0003003800084Q000800033Q00202Q00080008001A00122Q000900446Q000A3Q000600302Q000A001C004300122Q000B001E3Q00202Q000B000B000D001291000C00223Q001291000D00053Q001291000E00223Q001291000F00054Q008C010B000F0002001056000A001D000B003005000A00210022003005000A0010000A003005000A00360034001056000A002400072Q008C0108000A00020010560003004300082Q0070000800043Q0020100108000800450020100109000200460006FC000900FC0001000100049F012Q00FC0001002010010900030004002010010A00030004002010010B000300062Q008C0108000B00020010560003003900080006D400083Q000100032Q0018012Q00034Q00703Q00054Q00703Q00043Q0006D400090001000100032Q00703Q00044Q0018012Q00084Q00703Q00063Q001056000300470009002010010900030047001056000300480009000290010900023Q0010560003004900090006D400090003000100022Q00703Q00044Q0018012Q00083Q0010560003004A00090006D400090004000100012Q0018012Q00043Q0010560003004B00090006D400090005000100012Q0018012Q00043Q0010560003004C00090006D400090006000100022Q0018012Q00034Q00703Q00044Q001E000A000A3Q0006D4000B0007000100032Q0018012Q00034Q0018012Q000A4Q00703Q00053Q002004000C0004004D00202Q000C000C004E00202Q000E0003004300202Q000E000E004F00202Q000E000E00500006D400100008000100062Q0018012Q00044Q0018012Q00034Q00703Q00054Q0018012Q00094Q0018012Q000A4Q00703Q00074Q0072010E00104Q0061010C3Q000100204F000C0004004D00202Q000C000C004E4Q000E00073Q00202Q000E000E005100202Q000E000E00500006D400100009000100022Q0018012Q00034Q0018012Q000B4Q005A010E00106Q000C3Q00014Q000C5Q00202Q000D0004004D00202Q000D000D004E00202Q000F0004004300202Q000F000F005200202Q000F000F00500006D40011000A000100012Q0018012Q000C4Q003C010F00116Q000D3Q000100202Q000D0004004D00202Q000D000D004E00202Q000F0004004300202Q000F000F005300202Q000F000F00500006D40011000B000100012Q0018012Q000C4Q003C010F00116Q000D3Q000100202Q000D0004004D00202Q000D000D004E00202Q000F0003004300202Q000F000F005200202Q000F000F00500006D40011000C000100012Q0018012Q000C4Q003C010F00116Q000D3Q000100202Q000D0004004D00202Q000D000D004E00202Q000F0003004300202Q000F000F005300202Q000F000F00500006D40011000D000100012Q0018012Q000C4Q0072010F00114Q0061010D3Q0001002010010D00030008000EC8000500642Q01000D00049F012Q00642Q01002010010D000300082Q0085010D000D3Q001091010D0055000D0006FC000D00652Q01000100049F012Q00652Q01001291000D00223Q00105600030054000D00204F000D0004004D00202Q000D000D004E4Q000F00073Q00202Q000F000F004F00202Q000F000F00500006D40011000E000100032Q0018012Q000C4Q0018012Q00044Q0018012Q00034Q0072010F00114Q0061010D3Q00010006D4000D000F000100032Q0018012Q000B4Q0018012Q00044Q00703Q00063Q00106100030056000D4Q000D00086Q000E8Q000D0002000100202Q000D0002005700062Q000D007F2Q013Q00049F012Q007F2Q01002011000D0004004C2Q0065010F00014Q004D010D000F00012Q0070000D00063Q002002000D000D005800122Q000E00596Q000F00016Q001000036Q000D001000014Q000300028Q00013Q00103Q00133Q002Q033Q004D61782Q033Q004D696E028Q0003053Q0056616C756503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F03083Q00506F736974696F6E026Q00E03F03053Q0054772Q656E03043Q0046692Q6C03043Q004B6E6F622Q033Q0053657403073Q00526561646F757403043Q005465787403063Q00666F726D617403083Q00526F756E64696E6703063Q0053752Q666978014B4Q007000015Q0020102Q01000100012Q007000025Q0020100102000200022Q003Q01000100020026470001000A0001000300049F012Q000A0001001291000200033Q0006FC000200100001000100049F012Q001000012Q007000025Q0020310002000200044Q00035Q00202Q0003000300024Q0002000200034Q0002000200012Q002A01033Q0001001220010400063Q0020100104000400072Q0018010500023Q001291000600033Q001291000700083Q001291000800034Q008C0104000800020010560003000500042Q002A01043Q0001001220010500063Q0020100105000500072Q0018010600023Q001291000700033Q0012910008000A3Q001291000900034Q008C0105000900020010560004000900050006933Q003100013Q00049F012Q003100012Q0070000500013Q00207C00050005000B4Q00065Q00202Q00060006000C4Q000700036Q0005000700012Q0070000500013Q00207C00050005000B4Q00065Q00202Q00060006000D4Q000700046Q00050007000100049F012Q003D00012Q0070000500013Q00207C00050005000E4Q00065Q00202Q00060006000C4Q000700036Q0005000700012Q0070000500013Q00207C00050005000E4Q00065Q00202Q00060006000D4Q000700046Q0005000700012Q007000055Q0020A500050005000F4Q000600023Q00202Q0006000600114Q00075Q00202Q0007000700044Q00085Q00202Q0008000800124Q0006000800024Q00075Q00202Q0007000700132Q006B0106000600070010560005001000062Q0024012Q00017Q00113Q0003043Q007479706503063Q006E756D62657203053Q00636C616D7003053Q00726F756E6403083Q00526F756E64696E672Q033Q004D696E2Q033Q004D617803053Q0056616C756503093Q005F6472612Q67696E6703083Q0043612Q6C6261636B03053Q007063612Q6C03043Q007761726E03203Q005B4175726F72615D20736C696465722063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q004368616E67656403043Q004669726503043Q00466C616703373Q001220010300014Q0018010400014Q0089000300020002002696000300060001000200049F012Q000600012Q00AA012Q00024Q007000035Q0020100103000300032Q007000045Q0020100104000400042Q0018010500013Q00201001063Q00052Q008C01040006000200201001053Q000600201001063Q00072Q008C0103000600022Q00182Q0100033Q00201001033Q000800066A2Q0100150001000300049F012Q001500012Q00AA012Q00023Q0010563Q000800012Q004B010300013Q00202Q00043Q00094Q000400046Q00030002000100062Q000200350001000100049F012Q0035000100201001033Q000A0006930003002C00013Q00049F012Q002C00010012200103000B3Q00201001043Q000A2Q0018010500014Q00270003000500040006FC0003002C0001000100049F012Q002C00010012200105000C3Q0012800006000D3Q00122Q0007000E6Q000800046Q0007000200024Q0006000600074Q00050002000100201001033Q000F0020B10003000300104Q000500016Q0003000500014Q000300023Q00202Q00030003001000202Q00043Q00114Q000500016Q0003000500012Q00AA012Q00024Q0024012Q00017Q00013Q0003053Q0056616C756501033Q0020102Q013Q00012Q00AA2Q0100024Q0024012Q00017Q00053Q002Q033Q004D696E2Q033Q004D617803083Q0053657456616C756503053Q00636C616D7003053Q0056616C756503104Q0073000300013Q00104Q0002000200104Q0001000300202Q00033Q00034Q00055Q00202Q00050005000400202Q00063Q00054Q000700016Q000800026Q000500086Q00033Q00014Q000300016Q00048Q0003000200016Q00028Q00017Q00053Q0003043Q004D61696403043Q004769766503073Q004368616E67656403073Q00436F2Q6E65637403053Q0056616C7565020D4Q008E01025Q00202Q00020002000100202Q00020002000200202Q00043Q000300202Q0004000400044Q000600016Q000400066Q00023Q00014Q000200013Q00202Q00033Q00052Q00040102000200012Q00AA012Q00024Q0024012Q00017Q00013Q00030B3Q0053657444697361626C656402064Q000801025Q00202Q0002000200014Q000400016Q0002000400016Q00028Q00017Q000A3Q0003053Q00547261636B03103Q004162736F6C757465506F736974696F6E03013Q0058030C3Q004162736F6C75746553697A65028Q0003053Q0056616C756503053Q00636C616D70026Q00F03F2Q033Q004D696E2Q033Q004D6178011F4Q007000015Q0020102Q01000100010020102Q01000100020020102Q01000100032Q007000025Q0020100102000200010020100102000200040020100102000200030026EC0002000D0001000500049F012Q000D00012Q007000035Q0020100103000300062Q00AA010300024Q0070000300013Q0020340103000300074Q00043Q00014Q00040004000200122Q000500053Q00122Q000600086Q0003000600024Q00045Q00202Q0004000400094Q00055Q00202Q00050005000A2Q007000065Q0020100106000600092Q00660005000500064Q0005000300054Q0004000400054Q000400028Q00017Q000A3Q0003093Q005F6472612Q67696E670100030A3Q00446973636F2Q6E65637403053Q0054772Q656E03043Q004B6E6F6203043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q000840026Q00224000174Q00707Q0030053Q000100022Q00703Q00013Q0006933Q000A00013Q00049F012Q000A00012Q00703Q00013Q0020115Q00032Q0004012Q000200012Q001E8Q0095012Q00014Q00703Q00023Q0020535Q00044Q00015Q00202Q0001000100054Q00023Q000100122Q000300073Q00202Q00030003000800122Q000400093Q00122Q0005000A6Q00030005000200102Q0002000600036Q000200016Q00017Q00153Q0003083Q0044697361626C6564030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F75636803093Q005F6472612Q67696E672Q0103053Q0054772Q656E03043Q004B6E6F6203043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q000840026Q00264003083Q0053657456616C756503083Q00506F736974696F6E03013Q0058030C3Q00496E7075744368616E67656403073Q00436F2Q6E65637403043Q004D61696403043Q004769766501354Q007000015Q0020102Q01000100010006930001000500013Q00049F012Q000500012Q0024012Q00013Q0020102Q013Q0002001220010200033Q0020100102000200020020100102000200040006402Q0100120001000200049F012Q001200010020102Q013Q0002001220010200033Q0020100102000200020020100102000200050006402Q0100120001000200049F012Q001200012Q0024012Q00014Q0070000100013Q0030382Q01000600074Q000100023Q00202Q0001000100084Q000200013Q00202Q0002000200094Q00033Q000100122Q0004000B3Q00202Q00040004000C00122Q0005000D3Q00122Q0006000E4Q008C0104000600020010DA0003000A00044Q0001000300014Q000100013Q00202Q00010001000F4Q000300033Q00202Q00043Q001000202Q0004000400114Q000300046Q00013Q00014Q000100053Q0020102Q01000100120020110001000100130006D400033Q000100022Q00703Q00014Q00703Q00034Q00482Q01000300024Q000100046Q00015Q00202Q00010001001400202Q0001000100152Q0070000300044Q004D2Q01000300012Q0024012Q00013Q00013Q00083Q0003093Q005F6472612Q67696E67030D3Q0055736572496E7075745479706503043Q00456E756D030D3Q004D6F7573654D6F76656D656E7403053Q00546F75636803083Q0053657456616C756503083Q00506F736974696F6E03013Q0058011A4Q007000015Q0020102Q01000100010006FC000100050001000100049F012Q000500012Q0024012Q00013Q0020102Q013Q0002001220010200033Q0020100102000200020020100102000200040006402Q0100120001000200049F012Q001200010020102Q013Q0002001220010200033Q0020100102000200020020100102000200050006402Q0100120001000200049F012Q001200012Q0024012Q00014Q007000015Q0020110001000100062Q0070000300013Q00201001043Q00070020100104000400082Q00F6000300044Q00612Q013Q00012Q0024012Q00017Q00053Q0003093Q005F6472612Q67696E67030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F75636801144Q007000015Q0020102Q01000100010006FC000100050001000100049F012Q000500012Q0024012Q00013Q0020102Q013Q0002001220010200033Q0020100102000200020020100102000200040006402Q0100110001000200049F012Q001100010020102Q013Q0002001220010200033Q00201001020002000200201001020002000500066A2Q0100130001000200049F012Q001300012Q0070000100014Q005E2Q01000100012Q0024012Q00019Q003Q00034Q0065012Q00014Q0095017Q0024012Q00019Q003Q00034Q0065017Q0095017Q0024012Q00019Q003Q00034Q0065012Q00014Q0095017Q0024012Q00019Q003Q00034Q0065017Q0095017Q0024012Q00017Q00083Q0003083Q0044697361626C656403073Q004B6579436F646503043Q00456E756D03053Q00526967687403083Q0053657456616C756503053Q0056616C756503043Q005374657003043Q004C65667402283Q0006FC000100090001000100049F012Q000900012Q007000025Q0006930002000900013Q00049F012Q000900012Q0070000200013Q0020100102000200010006930002000A00013Q00049F012Q000A00012Q0024012Q00013Q00201001023Q0002001220010300033Q00201001030003000200201001030003000400066A010200190001000300049F012Q001900012Q0070000200023Q0020110002000200052Q0070000400023Q0020100104000400062Q0070000500023Q0020100105000500072Q009E0104000400052Q004D01020004000100049F012Q0027000100201001023Q0002001220010300033Q00201001030003000200201001030003000800066A010200270001000300049F012Q002700012Q0070000200023Q00203B0002000200054Q000400023Q00202Q0004000400064Q000500023Q00202Q0005000500074Q0004000400054Q0002000400012Q0024012Q00017Q00063Q0003043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C030A3Q00556E726567697374657203043Q00466C6167010E4Q008700018Q0001000100014Q000100013Q00202Q00010001000100202Q0001000100024Q00010002000100202Q00013Q000300202Q0001000100044Q0001000200014Q000100023Q00202Q00010001000500202Q00023Q00064Q0001000200016Q00017Q000C3Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C030A3Q00636F72652F466C61677303093Q00636F72652F5574696C030A3Q00636F72652F476C797068030B3Q00636F72652F486F746B6579030E3Q006F7665726C6179732F4C6179657203073Q002Q5F696E646578026Q0033402Q033Q006E6577012D4Q00182Q015Q001291000200014Q00890001000200022Q001801025Q001291000300024Q00890002000200022Q006500035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q00122Q000900086Q0008000200024Q00095Q00122Q000A00096Q0009000200024Q000A5Q00102Q000A000A000A001291000B000B3Q0006D4000C3Q0001000B2Q0018012Q000A4Q0018012Q00064Q0018012Q00044Q0018012Q00014Q0018012Q00024Q0018012Q00074Q0018012Q00054Q0018012Q00094Q0018012Q000B4Q0018012Q00034Q0018012Q00083Q001056000A000C000C2Q00AA010A00024Q0024012Q00013Q00013Q00623Q00030C3Q007365746D6574617461626C6503043Q005479706503083Q0044726F70646F776E03063Q0056616C75657303083Q00642Q6570436F707903053Q004D756C74692Q0103093Q00412Q6C6F774E752Q6C030A3Q0053656172636861626C65030B3Q00506C616365686F6C64657203043Q006E6F6E6503083Q0043612Q6C6261636B03073Q004368616E6765642Q033Q006E657703083Q0047726F7570626F782Q033Q00526F7703063Q00412Q64526F7703043Q005465787403053Q005469746C6503083Q0064726F70646F776E03073Q00542Q6F6C74697003073Q00456C656D656E7403053Q005769647468026Q005C4003043Q0050692Q6C2Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q00314003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030A3Q00616C7068612E77652Q6C034Q00030B3Q004C61796F75744F72646572026Q00F03F03063Q00506172656E7403043Q00536C6F7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C030A3Q0050692Q6C5374726F6B6503083Q0055495374726F6B6503053Q00436F6C6F72030C3Q00636F6C6F722E612Q63656E74030C3Q005472616E73706172656E637903093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203073Q00446973706C617903083Q00506F736974696F6E026Q001C40028Q00026Q0034C0030A3Q0054657874436F6C6F723303083Q00636F6C6F722E6869030C3Q00546578745472756E6361746503053Q004174456E6403043Q006D6F6E6F03083Q00466F6E744661636503043Q00466F6E7403023Q00756903073Q0043686576726F6E026Q00224003083Q00636F6C6F722E6C6F030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F026Q0014C003053Q0056616C756503063Q0069706169727303073Q0044656661756C7403043Q007479706503063Q006E756D62657203063Q005F7061696E7403043Q004D61696403043Q004769766503073Q00436F2Q6E65637403083Q0047657456616C756503083Q0053657456616C75652Q033Q0053657403093Q0053657456616C75657303093Q004F6E4368616E676564030B3Q0053657444697361626C656403053Q00436C6F736503043Q004F70656E03113Q004D6F75736542752Q746F6E31436C69636B030A3Q004D6F757365456E746572030A3Q004D6F7573654C6561766503073Q0044657374726F7903083Q0044697361626C656403083Q00526567697374657203063Q006F7074696F6E033E012Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q002A01046Q007000056Q008C0103000500020030050003000200032Q0070000400013Q0020100104000400050020100105000200040006FC0005000F0001000100049F012Q000F00012Q002A01056Q0089000400020002001056000300040004002010010400020006002696000400150001000700049F012Q001500012Q001200046Q0065010400013Q0010560003000600040020100104000200080026960004001B0001000700049F012Q001B00012Q001200046Q0065010400013Q001056000300080004002010010400020009002696000400210001000700049F012Q002100012Q001200046Q0065010400013Q00105600030009000400201001040002000A0006FC000400270001000100049F012Q002700010012910004000B3Q0010560003000A000400201001040002000C0010560003000C00042Q0070000400023Q00201001040004000E2Q00F20004000100020010560003000D00040010560003000F3Q0020100104000200100006FC0004003F0001000100049F012Q003F000100201100043Q00112Q002A01063Q00020020100107000200120006FC0007003B0001000100049F012Q003B00010020100107000200130006FC0007003B0001000100049F012Q003B0001001291000700143Q0010560006001200070020100107000200150010560006001500072Q008C0104000600020010560003001000040010560004001600030020100105000200170006FC000500450001000100049F012Q00450001001291000500184Q0070000600033Q00208201060006001A00122Q0007001B6Q00083Q000700302Q0008001C000300122Q0009001E3Q00202Q00090009001F4Q000A00053Q00122Q000B00206Q0009000B000200102Q0008001D00092Q0070000900033Q00203C00090009002200122Q000A00236Q00090002000200102Q0008002100094Q000900033Q00202Q00090009002200122Q000A00256Q00090002000200102Q00080024000900302Q00080012002600300500080027002800201001090004002A0010560008002900092Q008C0106000800020010560003001900062Q0070000600033Q00201001060006002B2Q0070000700043Q00201001070007002C0012910008002D4Q00890007000200020020100108000300192Q004D0106000800012Q00E3000600033Q00202Q00060006001A00122Q0007002F6Q00083Q00054Q000900043Q00202Q00090009002C00122Q000A00316Q00090002000200102Q00080030000900302Q000800320028003005000800330028001220010900353Q0020100109000900340020100109000900360010560008003400090020100109000300190010560008002900092Q008C0106000800020010560003002E00062Q0070000600033Q0020100106000600122Q002A01073Q00060030B30007001C001200122Q0008001E3Q00202Q00080008001F00122Q000900393Q00122Q000A003A6Q0008000A000200102Q00070038000800122Q0008001E3Q00202Q00080008000E00122Q000900283Q001291000A003B3Q001291000B00283Q001291000C003A4Q008C0108000C00020010560007001D00082Q0070000800033Q0020100108000800220012910009003D4Q00890008000200020010560007003C0008001220010800353Q00201001080008003E00201001080008003F0010560007003E0008002010010800030019001056000700290008001291000800404Q008C0106000800020010560003003700060020100106000300372Q0070000700043Q002010010700070042001291000800434Q00890007000200020010560006004100072Q0070000600053Q002010010600060044002010010700030019001291000800453Q001291000900464Q008C010600090002001056000300440006002010010600030044001220010700483Q00201001070007000E001291000800283Q001291000900494Q008C0107000900020010560006004700070020100106000300440012200107001E3Q00201001070007000E001291000800283Q0012910009004A3Q001291000A00493Q001291000B003A4Q008C0107000B0002001056000600380007002010010600030006000693000600C900013Q00049F012Q00C900012Q002A01065Q0010560003004B00060012200106004C3Q00201001070002004D0006FC000700C20001000100049F012Q00C200012Q002A01076Q005E00060002000800049F012Q00C60001002010010B0003004B0020F9000B000A0007000677000600C40001000200049F012Q00C4000100049F012Q00D4000100201001060002004D00109E0003004B000600122Q0006004E3Q00202Q00070003004B4Q00060002000200262Q000600D40001004F00049F012Q00D4000100201001060003000400201001070003004B2Q00160106000600070010560003004B00060006D400063Q000100012Q0018012Q00033Q0006D400070001000100032Q0018012Q00064Q0018012Q00034Q00703Q00043Q00102801030050000700202Q00080004005100202Q0008000800524Q000A00043Q00202Q000A000A000D00202Q000A000A00534Q000C00076Q000A000C6Q00083Q00010006D400080002000100032Q0018012Q00074Q0018012Q00034Q00703Q00063Q000290010900033Q0010560003005400090006D400090004000100032Q00703Q00014Q0018012Q00074Q0018012Q00083Q0010560003005500090020100109000300550010560003005600090006D400090005000100032Q00703Q00014Q0018012Q00074Q00703Q00073Q0010560003005700090006D400090006000100012Q0018012Q00043Q0010560003005800090006D400090007000100012Q0018012Q00043Q0010560003005900090006D400090008000100012Q00703Q00073Q0010560003005A00090006D4000900090001000A2Q0018012Q00044Q00703Q00074Q00703Q00034Q00703Q00044Q00703Q00014Q00703Q00084Q00703Q00094Q0018012Q00084Q0018012Q00024Q00703Q000A3Q0010560003005B000900200400090004005100202Q00090009005200202Q000B0003001900202Q000B000B005C00202Q000B000B00530006D4000D000A000100012Q0018012Q00034Q003C010B000D6Q00093Q000100202Q00090004005100202Q00090009005200202Q000B0003001900202Q000B000B005D00202Q000B000B00530006D4000D000B000100042Q0018012Q00044Q00703Q00094Q0018012Q00034Q00703Q00044Q003C010B000D6Q00093Q000100202Q00090004005100202Q00090009005200202Q000B0003001900202Q000B000B005E00202Q000B000B00530006D4000D000C000100032Q00703Q00094Q0018012Q00034Q00703Q00044Q0072010B000D4Q006101093Q00010006D40009000D000100022Q0018012Q00044Q00703Q00063Q0010810103005F00094Q000900076Q00090001000100202Q00090002006000062Q000900362Q013Q00049F012Q00362Q010020110009000400592Q0065010B00014Q004D0109000B00012Q0070000900063Q00200200090009006100122Q000A00626Q000B00016Q000C00036Q0009000C00014Q000300028Q00013Q000E3Q000E3Q0003053Q004D756C746903063Q0069706169727303063Q0056616C75657303053Q0056616C7565026Q00F03F028Q00030B3Q00506C616365686F6C646572027Q004003053Q007461626C6503063Q00636F6E63617403023Q002C2003093Q002073656C65637465640003083Q00746F737472696E6700394Q00707Q002010014Q00010006933Q002A00013Q00049F012Q002A00012Q002A016Q00120C2Q0100026Q00025Q00202Q0002000200034Q00010002000300044Q001200012Q007000065Q0020100106000600042Q00160106000600050006930006001200013Q00049F012Q001200012Q000100065Q0020600006000600052Q004A012Q000600050006770001000A0001000200049F012Q000A00012Q000100015Q0026470001001B0001000600049F012Q001B00012Q007000015Q0020102Q01000100072Q0065010200014Q00B6000100034Q000100015Q0026EC000100250001000800049F012Q002500010012202Q0100093Q0020C200010001000A4Q00025Q00122Q0003000B6Q0001000300024Q00028Q000100034Q000100015Q0012910002000C4Q006B2Q01000100022Q006501026Q00B6000100034Q00707Q002010014Q00040026473Q00320001000D00049F012Q003200012Q00707Q002010014Q00072Q00652Q0100014Q00B63Q00033Q001220012Q000E4Q007000015Q0020102Q01000100042Q00893Q000200022Q00652Q016Q00B63Q00034Q0024012Q00017Q00063Q0003073Q00446973706C617903043Q0054657874030A3Q0054657874436F6C6F72332Q033Q0047657403083Q00636F6C6F722E6C6F03083Q00636F6C6F722E686900154Q00708Q00F13Q000100012Q0070000200013Q002010010200020001001056000200024Q0070000200013Q0020100102000200010006930001000F00013Q00049F012Q000F00012Q0070000300023Q002010010300030004001291000400054Q00890003000200020006FC000300130001000100049F012Q001300012Q0070000300023Q002010010300030004001291000400064Q00890003000200020010560002000300032Q0024012Q00017Q00093Q0003083Q0047657456616C756503083Q0043612Q6C6261636B03053Q007063612Q6C03043Q007761726E03223Q005B4175726F72615D2064726F70646F776E2063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q004368616E67656403043Q004669726503043Q00466C616700234Q001E019Q002Q000100016Q00013Q00206Q00016Q000200024Q000100013Q00202Q00010001000200062Q0001001700013Q00049F012Q001700010012202Q0100034Q00BD000200013Q00202Q0002000200024Q00038Q00010003000200062Q000100170001000100049F012Q00170001001220010300043Q001280000400053Q00122Q000500066Q000600026Q0005000200024Q0004000400054Q0003000200012Q0070000100013Q00203300010001000700202Q0001000100084Q00038Q0001000300014Q000100023Q00207C0001000100084Q000200013Q00202Q0002000200094Q00038Q0001000300012Q0024012Q00017Q00033Q0003053Q004D756C746903053Q0056616C756503053Q007061697273010F3Q0020102Q013Q00010006FC000100050001000100049F012Q000500010020102Q013Q00022Q00AA2Q0100024Q002A2Q015Q001220010200033Q00201001033Q00022Q005E00020002000400049F012Q000B00012Q004A2Q01000500060006770002000A0001000200049F012Q000A00012Q00AA2Q0100024Q0024012Q00017Q000C3Q0003053Q004D756C746903043Q007479706503053Q007461626C65026Q00F03F0003063Q006970616972732Q0103053Q00706169727303053Q0056616C756503063Q006E756D62657203063Q0056616C75657303073Q00696E6465784F66033E3Q00201001033Q00010006930003002300013Q00049F012Q002300012Q002A01035Q001220010400024Q0018010500014Q0089000400020002002647000400210001000300049F012Q002100010020100104000100040026470004000D0001000500049F012Q000D00012Q001200046Q0065010400013Q0006930004001800013Q00049F012Q00180001001220010500064Q0018010600014Q005E00050002000700049F012Q001500010020F9000300090007000677000500140001000200049F012Q0014000100049F012Q00210001001220010500084Q0018010600014Q005E00050002000700049F012Q001F00010006930009001F00013Q00049F012Q001F00010020F90003000800070006770005001C0001000200049F012Q001C00010010563Q0009000300049F012Q00350001001220010300024Q0018010400014Q00890003000200020026470003002A0001000A00049F012Q002A000100201001033Q000B2Q00162Q0100030001002696000100340001000500049F012Q003400012Q007000035Q00206201030003000C00202Q00043Q000B4Q000500016Q00030005000200062Q000300340001000100049F012Q003400012Q00AA012Q00023Q0010563Q000900010006930002003A00013Q00049F012Q003A00012Q0070000300014Q005E01030001000100049F012Q003C00012Q0070000300024Q005E0103000100012Q00AA012Q00024Q0024012Q00017Q000B3Q0003063Q0056616C75657303083Q00642Q6570436F707903053Q004D756C746903053Q00706169727303053Q0056616C756503073Q00696E6465784F660003063Q0049734F70656E03043Q0050692Q6C03053Q00436C6F736503043Q004F70656E02334Q007000025Q00201001020002000200060B010300050001000100049F012Q000500012Q002A01036Q00890002000200020010563Q0001000200201001023Q00030006930002001A00013Q00049F012Q001A0001001220010200043Q00201001033Q00052Q005E00020002000400049F012Q001700012Q007000065Q00206201060006000600202Q00073Q00014Q000800056Q00060008000200062Q000600170001000100049F012Q0017000100201001063Q00050020F90006000500070006770002000E0001000100049F012Q000E000100049F012Q0025000100201001023Q0005002696000200250001000700049F012Q002500012Q007000025Q00200E00020002000600202Q00033Q000100202Q00043Q00054Q00020004000200062Q000200250001000100049F012Q002500010030053Q000500072Q0070000200014Q005E0102000100012Q00AD010200023Q00202Q00020002000800202Q00033Q00094Q00020002000200062Q0002003100013Q00049F012Q0031000100201100023Q000A2Q000401020002000100201100023Q000B2Q00040102000200012Q00AA012Q00024Q0024012Q00017Q00053Q0003043Q004D61696403043Q004769766503073Q004368616E67656403073Q00436F2Q6E65637403083Q0047657456616C7565020E4Q007B01025Q00202Q00020002000100202Q00020002000200202Q00043Q000300202Q0004000400044Q000600016Q000400066Q00023Q00014Q000200013Q00202Q00033Q00052Q00F6000300044Q006101023Q00012Q00AA012Q00024Q0024012Q00017Q00013Q00030B3Q0053657444697361626C656402064Q000801025Q00202Q0002000200014Q000400016Q0002000400016Q00028Q00017Q00033Q0003063Q0049734F70656E03043Q0050692Q6C03053Q00436C6F7365010A4Q00AD2Q015Q00202Q00010001000100202Q00023Q00024Q00010002000200062Q0001000900013Q00049F012Q000900012Q007000015Q0020102Q01000100032Q005E2Q01000100012Q0024012Q00017Q00533Q0003083Q0044697361626C656403063Q0049734F70656E03043Q0050692Q6C03053Q00436C6F7365030A3Q0053656172636861626C65026Q003A40028Q002Q033Q004E657703053Q004672616D6503043Q004E616D6503043Q004C69737403043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F03163Q004261636B67726F756E645472616E73706172656E637903083Q00506F736974696F6E030A3Q0066726F6D4F2Q66736574026Q001040026Q0020C0026Q00324003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E77652Q6C03063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03043Q005465787403063Q00536561726368026Q001840026Q0028C0034Q00030F3Q00506C616365686F6C6465725465787403063Q0066696C74657203113Q00506C616365686F6C646572436F6C6F723303083Q00636F6C6F722E6C6F030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903103Q00436C656172546578744F6E466F637573010003023Q00756903073Q0054657874426F78030E3Q005363726F2Q6C696E674672616D6503073Q004F7074696F6E73030A3Q0043616E76617353697A6503133Q004175746F6D6174696343616E76617353697A6503043Q00456E756D030D3Q004175746F6D6174696353697A6503013Q005903123Q005363726F2Q6C426172546869636B6E652Q73030E3Q0073697A652E7363726F2Q6C62617203143Q005363726F2Q6C426172496D616765436F6C6F7233031A3Q005363726F2Q6C426172496D6167655472616E73706172656E6379029A5Q99D93F03073Q0050612Q64696E67026Q00084003043Q006D6174682Q033Q006D61782Q033Q006D696E03063Q0056616C756573026Q001C40030D3Q0073697A652E706F7075704D617803053Q0054772Q656E030A3Q0050692Q6C5374726F6B65030C3Q005472616E73706172656E637903073Q0043686576726F6E03083Q00526F746174696F6E025Q0080664003043Q004F70656E03053Q007769647468030C3Q004162736F6C75746553697A6503013Q0058030A3Q00506F7075705769647468025Q00805D4003053Q00616C69676E03053Q00726967687403073Q006F6E436C6F736503073Q00466F637573656403073Q00436F2Q6E65637403093Q00466F6375734C6F737403183Q0047657450726F70657274794368616E6765645369676E616C010E013Q007000015Q0020102Q01000100010006930001000500013Q00049F012Q000500012Q0024012Q00014Q0070000100013Q0020102Q010001000200201001023Q00032Q00890001000200020006930001000F00013Q00049F012Q000F00012Q0070000100013Q0020102Q01000100042Q005E2Q01000100012Q0024012Q00013Q0020102Q013Q00050006930001001500013Q00049F012Q00150001001291000100063Q0006FC000100160001000100049F012Q00160001001291000100074Q0070000200023Q00205D01020002000800122Q000300096Q00043Q000300302Q0004000A000B00122Q0005000D3Q00202Q00050005000E00122Q0006000F3Q00122Q000700073Q00122Q000800073Q00122Q000900076Q00050009000200102Q0004000C000500302Q00040010000F4Q0002000400024Q000300033Q00202Q00043Q000500062Q0004007300013Q00049F012Q007300012Q0070000400023Q0020100104000400080012DF000500096Q00063Q000500122Q0007000D3Q00202Q00070007001200122Q000800133Q00122Q000900136Q00070009000200102Q00060011000700122Q0007000D3Q00202Q00070007000E0012910008000F3Q001291000900143Q001291000A00073Q001291000B00154Q008C0107000B00020010560006000C00072Q0070000700023Q002010010700070017001291000800184Q00890007000200020010560006001600072Q0070000700023Q002010010700070017001291000800194Q00D600070002000200102Q00060010000700102Q0006001A00024Q0004000600024Q000500023Q00202Q00050005001B4Q000600033Q00202Q00060006001C00122Q0007001D6Q0006000200022Q0018010700044Q004D0105000700012Q0070000500023Q00201001050005001E2Q002A01063Q00090030B30006000A001F00122Q0007000D3Q00202Q00070007001200122Q000800203Q00122Q000900076Q00070009000200102Q00060011000700122Q0007000D3Q00202Q00070007000E00122Q0008000F3Q001291000900213Q001291000A000F3Q001291000B00074Q008C0107000B00020010560006000C000700304E0006001E002200302Q0006002300244Q000700033Q00202Q00070007001C00122Q000800266Q00070002000200102Q0006002500074Q000700023Q00202Q00070007001700122Q000800284Q008900070002000200105600060027000700300500060029002A0010560006001A00040012910007002B3Q0012910008002C4Q008C0105000800022Q0018010300054Q0070000400023Q0020100104000400080012910005002D4Q002A01063Q00090030050006000A002E0012200107000D3Q002010010700070012001291000800074Q0018010900014Q008C0107000900020010560006001100070012200107000D3Q00201001070007000E0012910008000F3Q001291000900073Q001291000A000F4Q0085010B00014Q008C0107000B00020010560006000C00070012200107000D3Q00201001070007000E2Q00F20007000100020010560006002F0007001220010700313Q00201001070007003200206801070007003300102Q0006003000074Q000700033Q00202Q00070007001C00122Q000800356Q00070002000200102Q0006003400074Q000700033Q00202Q00070007001C00122Q000800264Q00890007000200020010560006003600070030050006003700380010560006001A00022Q008C0104000600022Q0070000500023Q0020100105000500392Q0018010600043Q0012910007003A3Q0012910008003A3Q0012910009003A3Q001291000A003A4Q004D0105000A00012Q0070000500023Q00201001050005000B2Q0018010600043Q001291000700074Q004D0105000700012Q002A01055Q0006D400063Q0001000A2Q0018012Q00044Q0018012Q00054Q0018017Q00703Q00044Q00703Q00024Q00703Q00054Q00703Q00034Q00703Q00064Q00703Q00074Q00703Q00014Q0019000700066Q000800086Q00070002000100122Q0007003B3Q00202Q00070007003C00122Q0008000F3Q00122Q0009003B3Q00202Q00090009003D00202Q000A3Q003E4Q000A000A3Q00122Q000B003F6Q0009000B6Q00073Q000200122Q0008003B3Q00202Q00080008003D4Q000900033Q00202Q00090009001C00122Q000A00406Q0009000200024Q000A00056Q000A0007000A00202Q000A000A00204Q0008000A00024Q00080008000100122Q0009000D3Q00202Q00090009000E00122Q000A000F3Q00122Q000B00073Q00122Q000C00076Q000D00086Q0009000D000200102Q0002000C00094Q000900063Q00202Q00090009004100202Q000A3Q00424Q000B3Q000100302Q000B004300074Q0009000B00014Q000900063Q00202Q00090009004100202Q000A3Q00444Q000B3Q000100302Q000B004500464Q0009000B00014Q000900013Q00202Q00090009004700202Q000A3Q00034Q000B00026Q000C3Q000300122Q000D003B3Q00202Q000D000D003C00202Q000E3Q000300202Q000E000E004900202Q000E000E004A4Q000F00083Q00202Q000F000F004B00062Q000F00EF0001000100049F012Q00EF0001001291000F004C4Q008C010D000F0002001056000C0048000D003005000C004D004E0006D4000D0001000100042Q00703Q00064Q0018017Q0018012Q00034Q00703Q00093Q001056000C004F000D2Q004D0109000C00010006930003000D2Q013Q00049F012Q000D2Q010020100109000300500020110009000900510006D4000B0002000100012Q00703Q00094Q004D0109000B00010020100109000300520020110009000900510006D4000B0003000100012Q00703Q00094Q004D0109000B0001002011000900030053001291000B001E4Q008C0109000B00020020110009000900510006D4000B0004000100022Q0018012Q00064Q0018012Q00034Q004D0109000B00012Q0024012Q00013Q00053Q00323Q0003063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q004775694F626A65637403073Q0044657374726F7903063Q0056616C756573034Q0003053Q0066752Q7A79026Q00F03F028Q0003043Q0054657874030A3Q006E6F206D617463686573030A3Q0054657874436F6C6F723303053Q00546F6B656E03083Q00636F6C6F722E6C6F03043Q0053697A6503053Q005544696D322Q033Q006E657703083Q00506F736974696F6E030A3Q0066726F6D4F2Q66736574026Q00184003063Q00506172656E7403053Q004D756C746903053Q0056616C75652Q012Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503083Q00746F737472696E6703103Q004261636B67726F756E64436F6C6F7233030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030B3Q004C61796F75744F7264657203063Q00436F726E6572026Q000840026Q001C40026Q002CC02Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403093Q00636F6C6F722E6D6964030C3Q00546578745472756E6361746503043Q00456E756D03053Q004174456E64030A3Q004D6F757365456E74657203073Q00436F2Q6E656374030A3Q004D6F7573654C6561766503113Q004D6F75736542752Q746F6E31436C69636B03063Q0062752Q746F6E03043Q007465787403053Q0076616C756501CC3Q0012072Q0100016Q00025Q00202Q0002000200024Q000200036Q00013Q000300044Q000D0001002011000600050003001291000800044Q008C0106000800020006930006000D00013Q00049F012Q000D00010020110006000500052Q0004010600020001000677000100060001000200049F012Q000600012Q002A2Q016Q00952Q0100014Q00602Q015Q00122Q000200016Q000300023Q00202Q0003000300064Q00020002000400044Q002500010006933Q002200013Q00049F012Q002200010026963Q00220001000700049F012Q002200012Q0070000700033Q0020620007000700084Q00088Q000900066Q00070009000200062Q0007002500013Q00049F012Q002500012Q0001000700013Q0020600007000700092Q004A2Q0100070006000677000200170001000200049F012Q001700012Q0001000200013Q002647000200450001000A00049F012Q004500012Q0070000200043Q00201001020002000B2Q002A01033Q00050030050003000B000C2Q0070000400043Q00201001040004000E0012910005000F4Q00890004000200020010560003000D0004001220010400113Q002010010400040012001291000500093Q0012910006000A3Q0012910007000A4Q0070000800054Q008C010400080002001056000300100004001220010400113Q002010010400040014001291000500153Q0012910006000A4Q008C0104000600020010560003001300042Q007000045Q0010560003001600042Q00040102000200012Q0024012Q00013Q001220010200014Q0018010300014Q005E00020002000400049F012Q00C900012Q0070000700023Q0020100107000700170006930007005200013Q00049F012Q005200012Q0070000700023Q0020100107000700182Q0016010700070006002696000700570001001900049F012Q005700012Q0070000700023Q002010010700070018000640010700570001000600049F012Q005700012Q001200076Q0065010700014Q0070000800043Q00201001080008001A0012910009001B4Q002A010A3Q0007001220010B001D4Q0018010C00064Q0089000B00020002001056000A001C000B001220010B00113Q002010010B000B0012001291000C00093Q001291000D000A3Q001291000E000A4Q0070000F00054Q008C010B000F0002001056000A0010000B2Q0070000B00043Q002010010B000B000E001291000C001F4Q0089000B00020002001056000A001E000B003005000A00200009003005000A000B0007001056000A002100052Q0070000B5Q001056000A0016000B2Q008C0108000A00022Q0070000900043Q002010010900090022001291000A00234Q0018010B00084Q004D0109000B00012Q0070000900043Q00201001090009000B2Q002A010A3Q0006001220010B00113Q002010010B000B0014001291000C00243Q0012E5000D000A6Q000B000D000200102Q000A0013000B00122Q000B00113Q00202Q000B000B001200122Q000C00093Q00122Q000D00253Q00122Q000E00093Q00122Q000F000A6Q000B000F0002001056000A0010000B001220010B001D4Q0018010C00064Q0089000B00020002001056000A000B000B0006930007009500013Q00049F012Q009500012Q0070000B00063Q002010010B000B0026001291000C00274Q0089000B000200020006FC000B00990001000100049F012Q009900012Q0070000B00063Q002010010B000B0026001291000C00284Q0089000B00020002001056000A000D000B0012C9000B002A3Q00202Q000B000B002900202Q000B000B002B00102Q000A0029000B00102Q000A001600084Q00090002000200202Q000A0008002C00202Q000A000A002D0006D4000C3Q000100062Q00703Q00074Q0018012Q00084Q00703Q00064Q00703Q00024Q0018012Q00064Q0018012Q00094Q004D010A000C0001002010010A0008002E002011000A000A002D0006D4000C0001000100062Q00703Q00074Q0018012Q00084Q00703Q00024Q0018012Q00064Q0018012Q00094Q00703Q00064Q004D010A000C0001002010010A0008002F002011000A000A002D0006D4000C0002000100062Q00703Q00024Q0018012Q00064Q0018012Q00094Q00703Q00064Q00703Q00084Q00703Q00094Q004D010A000C00012Q0070000A00014Q0070000B00014Q0001000B000B3Q002060000B000B00092Q002A010C3Q0003001056000C00300008001056000C00310009001056000C003200062Q004A010A000B000C2Q00A801076Q00A801055Q000677000200490001000200049F012Q004900012Q0024012Q00013Q00033Q00083Q0003053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030E3Q00616C7068612E726F77486F76657203053Q004D756C746903053Q0056616C7565030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686900244Q009D7Q00206Q00014Q000100016Q00023Q00014Q000300023Q00202Q00030003000300122Q000400046Q00030002000200102Q0002000200036Q000200012Q00703Q00033Q002010014Q00050006933Q001400013Q00049F012Q001400012Q00703Q00033Q002010014Q00062Q0070000100044Q0016014Q00010006FC3Q00230001000100049F012Q002300012Q00703Q00033Q002010014Q00062Q0070000100043Q000640012Q00230001000100049F012Q002300012Q00707Q00204C014Q00014Q000100056Q00023Q00014Q000300023Q00202Q00030003000300122Q000400086Q00030002000200102Q0002000700036Q000200012Q0024012Q00017Q00093Q0003053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03053Q004D756C746903053Q0056616C7565030A3Q0054657874436F6C6F72332Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403093Q00636F6C6F722E6D6964002A4Q00387Q00206Q00014Q000100016Q00023Q000100302Q0002000200036Q000200016Q00023Q00206Q000400064Q001000013Q00049F012Q001000012Q00703Q00023Q002010014Q00052Q0070000100034Q0016014Q00010006FC3Q00170001000100049F012Q001700012Q00703Q00023Q002010014Q00052Q0070000100033Q000640012Q00160001000100049F012Q001600012Q00128Q0065012Q00014Q007000015Q0020102Q01000100012Q0070000200044Q002A01033Q00010006933Q002300013Q00049F012Q002300012Q0070000400053Q002010010400040007001291000500084Q00890004000200020006FC000400270001000100049F012Q002700012Q0070000400053Q002010010400040007001291000500094Q00890004000200020010560003000600042Q004D2Q01000300012Q0024012Q00017Q00093Q0003053Q004D756C746903053Q0056616C7565030A3Q0054657874436F6C6F72332Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403093Q00636F6C6F722E6D696403093Q00412Q6C6F774E752Q6C0003053Q00436C6F7365003C4Q00707Q002010014Q00010006933Q002700013Q00049F012Q002700012Q00707Q002010014Q00022Q0042000100016Q00025Q00202Q0002000200024Q000300016Q00020002000300062Q0002001000013Q00049F012Q001000012Q001E000200023Q00049F012Q001100012Q001200026Q0065010200014Q004A012Q000100022Q00423Q00026Q00015Q00202Q0001000100024Q000200016Q00010001000200062Q0001001F00013Q00049F012Q001F00012Q0070000100033Q0020102Q0100010004001291000200054Q00890001000200020006FC000100230001000100049F012Q002300012Q0070000100033Q0020102Q0100010004001291000200064Q00890001000200020010563Q000300012Q00703Q00044Q005E012Q0001000100049F012Q003B00012Q00707Q002010014Q00070006933Q003300013Q00049F012Q003300012Q00707Q002010014Q00022Q0070000100013Q00066A012Q00330001000100049F012Q003300012Q00707Q0030053Q0002000800049F012Q003600012Q00708Q0070000100013Q0010563Q000200012Q00703Q00044Q005E012Q000100012Q00703Q00053Q002010014Q00092Q005E012Q000100012Q0024012Q00017Q00083Q0003053Q0054772Q656E030A3Q0050692Q6C5374726F6B65030C3Q005472616E73706172656E6379026Q00F03F03073Q0043686576726F6E03083Q00526F746174696F6E028Q00030F3Q00466F726365556E73752Q7072652Q7300154Q00707Q002010014Q00012Q0070000100013Q0020102Q01000100022Q002A01023Q00010030050002000300042Q004D012Q000200012Q00707Q002010014Q00012Q0070000100013Q0020102Q01000100052Q002A01023Q00010030050002000600072Q004D012Q000200012Q00703Q00023Q0006933Q001400013Q00049F012Q001400012Q00703Q00033Q002010014Q00082Q005E012Q000100012Q0024012Q00017Q00013Q00030D3Q0053657453752Q7072652Q73656400054Q00707Q002010014Q00012Q00652Q0100014Q0004012Q000200012Q0024012Q00017Q00013Q00030D3Q0053657453752Q7072652Q73656400054Q00707Q002010014Q00012Q00652Q016Q0004012Q000200012Q0024012Q00017Q00013Q0003043Q005465787400054Q00B99Q00000100013Q00202Q0001000100016Q000200016Q00017Q00013Q0003043Q004F70656E00044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00063Q0003083Q0044697361626C656403053Q0054772Q656E03043Q0050692Q6C03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030F3Q00616C7068612E77652Q6C486F76657200114Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002078014Q00024Q000100023Q00202Q0001000100034Q00023Q00014Q000300033Q00202Q00030003000500122Q000400066Q00030002000200102Q0002000400036Q000200016Q00017Q00053Q0003053Q0054772Q656E03043Q0050692Q6C03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030A3Q00616C7068612E77652Q6C000C4Q0035016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q00014Q000300023Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200016Q00017Q00073Q0003053Q00436C6F736503043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C030A3Q00556E726567697374657203043Q00466C6167010E3Q00201100013Q00012Q00042Q01000200012Q00BA00015Q00202Q00010001000200202Q0001000100034Q00010002000100202Q00013Q000400202Q0001000100054Q0001000200014Q000100013Q00202Q00010001000600202Q00023Q00072Q00042Q01000200012Q0024012Q00017Q00103Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C030A3Q00636F72652F466C61677303093Q00636F72652F5574696C030B3Q00636F72652F486F746B6579030E3Q006F7665726C6179732F4C6179657203073Q002Q5F696E64657803043Q00486F6C6403063Q00546F2Q676C6503063Q00416C7761797303063Q004F6E486F6C6403083Q0052656769737472792Q033Q006E6577030D3Q00436C656172526567697374727901334Q00182Q015Q001291000200014Q00890001000200022Q006500025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q00122Q000900086Q0008000200024Q00095Q00102Q0009000900092Q002A010A00043Q001291000B000A3Q001291000C000B3Q001291000D000C3Q001291000E000D4Q0025000A000400012Q002A010B5Q0010560009000E000B0006D4000B3Q0001000A2Q0018012Q00094Q0018012Q00044Q0018012Q00014Q0018012Q00024Q0018012Q00064Q0018012Q00034Q0018012Q00054Q0018012Q000A4Q0018012Q00074Q0018012Q00083Q0010560009000F000B0006D4000B0001000100012Q0018012Q00093Q00105600090010000B2Q00AA010900024Q0024012Q00013Q00023Q005C3Q00030C3Q007365746D6574617461626C6503043Q005479706503093Q004B65795069636B657203043Q004D6F646503063Q00546F2Q676C6503043Q004E6F55492Q0103083Q0043612Q6C6261636B03073Q00436C69636B65642Q033Q006E657703073Q004368616E67656403083Q0047726F7570626F782Q033Q00526F7703063Q00412Q64526F7703043Q005465787403053Q005469746C6503073Q006B657962696E6403073Q00542Q6F6C74697003053Q004C6162656C03043Q0062696E642Q033Q004B65790003073Q0044656661756C7403083Q00746F737472696E6703053Q007063612Q6C03043Q0048656C64010003073Q00546F2Q676C656403093Q00436170747572696E6703063Q0042752Q746F6E2Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q005040026Q003140030D3Q004175746F6D6174696353697A6503043Q00456E756D03013Q005803103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030A3Q00616C7068612E77652Q6C034Q00030B3Q004C61796F75744F72646572027Q004003063Q00506172656E7403043Q00536C6F7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03073Q0050612Q64696E67028Q00026Q00184003063Q005374726F6B6503083Q0055495374726F6B6503053Q00436F6C6F72030C3Q00636F6C6F722E612Q63656E74030C3Q005472616E73706172656E6379026Q00F03F03093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503063Q00426F72646572030A3Q006B6579203A206E6F6E65030A3Q0054657874436F6C6F723303093Q00636F6C6F722E6D696403043Q006D6F6E6F03083Q00476574537461746503073Q004B65794E616D6503063Q005F7061696E7403043Q004D61696403043Q004769766503073Q00436F2Q6E65637403083Q0053657456616C75652Q033Q0053657403083Q0047657456616C756503073Q005365744D6F646503093Q004F6E4368616E67656403073Q004F6E436C69636B030B3Q0053657444697361626C656403113Q004D6F75736542752Q746F6E31436C69636B03113Q004D6F75736542752Q746F6E32436C69636B030A3Q004D6F757365456E746572030A3Q004D6F7573654C6561766503073Q0044657374726F7903083Q0044697361626C656403083Q00526567697374727903083Q00526567697374657203063Q00746F2Q676C65033F012Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q002A01046Q007000056Q008C0103000500020030050003000200030020100104000200040006FC0004000D0001000100049F012Q000D0001001291000400053Q001056000300040004002010010400020006002696000400120001000700049F012Q001200012Q001200046Q0065010400013Q0010560003000600040020100104000200080010560003000800042Q0070000400013Q00201001040004000A2Q00F20004000100020010560003000900042Q0070000400013Q00201001040004000A2Q00F20004000100020010560003000B00040010560003000C3Q00201001040002000D0006FC0004002F0001000100049F012Q002F000100201100043Q000E2Q002A01063Q000200201001070002000F0006FC0007002B0001000100049F012Q002B00010020100107000200100006FC0007002B0001000100049F012Q002B0001001291000700113Q0010560006000F00070020100107000200120010560006001200072Q008C0104000600020010560003000D000400201001050002000F0006FC000500370001000100049F012Q0037000100201001050004000F0006FC000500370001000100049F012Q00370001001291000500143Q0010560003001300050030050003001500160020100105000200170006930005005300013Q00049F012Q00530001001220010500183Q0020100106000200172Q0089000500020002001220010600193Q0006D400073Q000100012Q0018012Q00054Q005E0006000200070006930006004900013Q00049F012Q004900010006930007004900013Q00049F012Q0049000100105600030015000700049F012Q00520001001220010800193Q0006D400090001000100012Q0018012Q00054Q005E0008000200090006930008005200013Q00049F012Q005200010006930009005200013Q00049F012Q005200010010560003001500092Q00A801055Q0030050003001A001B0030050003001C001B0030050003001D001B2Q006B000500023Q00202Q00050005001F00122Q000600206Q00073Q000800302Q00070021000300122Q000800233Q00202Q00080008002400122Q000900253Q00122Q000A00266Q0008000A0002001056000700220008001220010800283Q00201001080008002700206801080008002900102Q0007002700084Q000800023Q00202Q00080008002B00122Q0009002C6Q00080002000200102Q0007002A00084Q000800023Q00202Q00080008002B00122Q0009002E4Q00890008000200020010560007002D00080030050007000F002F0030050007003000310020100108000400330010560007003200082Q008C0105000700020010560003001E00052Q0070000500023Q0020100105000500342Q0070000600033Q002010010600060035001291000700364Q008900060002000200201001070003001E2Q004D0105000700012Q0070000500023Q00201001050005003700201001060003001E001291000700383Q001291000800393Q001291000900383Q001291000A00394Q004D0105000A00012Q00E3000500023Q00202Q00050005001F00122Q0006003B6Q00073Q00054Q000800033Q00202Q00080008003500122Q0009003D6Q00080002000200102Q0007003C000800302Q0007003E003F00300500070040003F001220010800283Q00201001080008004100201001080008004200105600070041000800201001080003001E0010560007003200082Q008C0105000700020010560003003A00052Q0070000500023Q00201001050005000F2Q002A01063Q000600300500060021000F001220010700233Q00201001070007000A001291000800383Q001291000900383Q001291000A003F3Q001291000B00384Q008C0107000B0002001056000600220007001220010700283Q0020100107000700270020100107000700290010560006002700070030050006000F00432Q0070000700023Q00201001070007002B001291000800454Q00D200070002000200102Q00060044000700202Q00070003001E00102Q00060032000700122Q000700466Q00050007000200102Q0003000F0005000290010500023Q0010560003004700050006D400050003000100012Q00703Q00043Q0010560003004800050006D400050004000100032Q0018012Q00034Q00703Q00034Q00703Q00053Q00102801030049000500202Q00060004004A00202Q00060006004B4Q000800033Q00202Q00080008000B00202Q00080008004C4Q000A00056Q0008000A6Q00063Q00010006D400060005000100022Q0018012Q00034Q00703Q00063Q0006D400070006000100022Q0018012Q00054Q0018012Q00063Q0010560003004D000700201001070003004D0010560003004E0007000290010700073Q0010560003004F00070006D400070008000100042Q00703Q00044Q00703Q00074Q0018012Q00054Q0018012Q00063Q0010560003005000070006D400070009000100012Q0018012Q00043Q0010560003005100070006D40007000A000100012Q0018012Q00043Q0010560003005200070006D40007000B000100012Q0018012Q00043Q0010560003005300070006D40007000C000100052Q0018012Q00034Q00703Q00084Q0018012Q00054Q0018012Q00064Q0018012Q00043Q00201001080003004D0006D40009000D000100022Q0018012Q00084Q0018012Q00073Q0010560003004D000900201001090003004D0010560003004E000900200400090004004A00202Q00090009004B00202Q000B0003001E00202Q000B000B005400202Q000B000B004C0006D4000D000E000100042Q0018012Q00044Q0018012Q00034Q0018012Q00054Q00703Q00084Q003C010B000D6Q00093Q000100202Q00090004004A00202Q00090009004B00202Q000B0003001E00202Q000B000B005500202Q000B000B004C0006D4000D000F000100072Q0018012Q00044Q00703Q00024Q00703Q00074Q0018012Q00034Q00703Q00034Q00703Q00054Q00703Q00094Q003C010B000D6Q00093Q000100202Q00090004004A00202Q00090009004B00202Q000B0003001E00202Q000B000B005600202Q000B000B004C0006D4000D0010000100042Q0018012Q00044Q00703Q00054Q0018012Q00034Q00703Q00034Q003C010B000D6Q00093Q000100202Q00090004004A00202Q00090009004B00202Q000B0003001E00202Q000B000B005700202Q000B000B004C0006D4000D0011000100032Q00703Q00054Q0018012Q00034Q00703Q00034Q0072010B000D4Q006101093Q00010006D400090012000100032Q00708Q0018012Q00044Q00703Q00063Q0010560003005800092Q0018010900054Q005E0109000100012Q0018010900074Q005E0109000100010020100109000200590006930009002D2Q013Q00049F012Q002D2Q010020110009000400532Q0065010B00014Q004D0109000B00010020100109000300060006FC000900372Q01000100049F012Q00372Q012Q007000095Q00201001090009005A2Q0070000A5Q002010010A000A005A2Q0001000A000A3Q002060000A000A003F2Q004A0109000A00032Q0070000900063Q00200200090009005B00122Q000A005C6Q000B00016Q000C00036Q0009000C00014Q000300028Q00013Q00133Q00023Q0003043Q00456E756D03073Q004B6579436F646500063Q0012DB3Q00013Q00206Q00024Q00019Q003Q00016Q00028Q00017Q00023Q0003043Q00456E756D030D3Q0055736572496E7075745479706500063Q0012DB3Q00013Q00206Q00024Q00019Q003Q00016Q00028Q00017Q00073Q002Q033Q004B65790003043Q004D6F646503063Q00416C7761797303063Q00546F2Q676C6503073Q00546F2Q676C656403043Q0048656C6401123Q0020102Q013Q0001002647000100050001000200049F012Q000500012Q00652Q016Q00AA2Q0100023Q0020102Q013Q00030026470001000A0001000400049F012Q000A00012Q00652Q0100014Q00AA2Q0100023Q0020102Q013Q00030026470001000F0001000500049F012Q000F00010020102Q013Q00062Q00AA2Q0100023Q0020102Q013Q00072Q00AA2Q0100024Q0024012Q00017Q00023Q0003073Q006B65794E616D652Q033Q004B657901064Q007000015Q0020102Q010001000100201001023Q00022Q00562Q0100024Q003500016Q0024012Q00017Q000F3Q0003093Q00436170747572696E6703043Q005465787403093Q006B6579203A203Q2E030A3Q0054657874436F6C6F72332Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403053Q0054772Q656E03063Q005374726F6B65030C3Q005472616E73706172656E6379028Q0003063Q006B6579203A2003073Q004B65794E616D6503083Q00476574537461746503093Q00636F6C6F722E6D6964026Q00F03F003C4Q00707Q002010014Q00010006933Q001600013Q00049F012Q001600012Q00707Q0020C65Q000200304Q000200039Q0000206Q00024Q000100013Q00202Q00010001000500122Q000200066Q00010002000200104Q000400016Q00023Q00206Q00074Q00015Q00202Q0001000100084Q00023Q000100302Q00020009000A6Q000200016Q00014Q00707Q002010014Q00020012810001000B6Q00025Q00202Q00020002000C4Q0002000200024Q00010001000200104Q000200012Q00707Q0020115Q000D2Q00893Q000200022Q0070000100023Q0020102Q01000100072Q007000025Q0020100102000200022Q002A01033Q00010006933Q002E00013Q00049F012Q002E00012Q0070000400013Q002010010400040005001291000500064Q00890004000200020006FC000400320001000100049F012Q003200012Q0070000400013Q0020100104000400050012910005000E4Q00890004000200020010560003000400042Q004D2Q01000300012Q0070000100023Q0020102Q01000100072Q007000025Q0020100102000200082Q002A01033Q000100300500030009000F2Q004D2Q01000300012Q0024012Q00017Q00093Q0003083Q00476574537461746503083Q0043612Q6C6261636B03053Q007063612Q6C03043Q007761726E03233Q005B4175726F72615D206B65797069636B65722063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q004368616E67656403043Q004669726503043Q00466C616700214Q0039016Q00206Q00016Q000200024Q00015Q00202Q00010001000200062Q0001001500013Q00049F012Q001500010012202Q0100034Q00BD00025Q00202Q0002000200024Q00038Q00010003000200062Q000100150001000100049F012Q00150001001220010300043Q001280000400053Q00122Q000500066Q000600026Q0005000200024Q0004000400054Q0003000200012Q007000015Q00203300010001000700202Q0001000100084Q00038Q0001000300014Q000100013Q00207C0001000100084Q00025Q00202Q0002000200094Q00038Q0001000300012Q0024012Q00017Q000C3Q0003043Q007479706503063Q00737472696E6703043Q006E6F6E65034Q002Q033Q004B65790003053Q007063612Q6C03043Q004E616D6503073Q00556E6B6E6F776E03043Q0048656C64010003073Q00546F2Q676C6564032E3Q001220010300014Q0018010400014Q0089000300020002002647000300230001000200049F012Q00230001002696000100090001000300049F012Q000900010026470001000B0001000400049F012Q000B00010030053Q0005000600049F012Q00240001001220010300073Q0006D400043Q000100012Q0018012Q00014Q005E0003000200040006930003001800013Q00049F012Q001800010006930004001800013Q00049F012Q00180001002010010500040008002696000500180001000900049F012Q001800010010563Q0005000400049F012Q00240001001220010500073Q0006D400060001000100012Q0018012Q00014Q005E0005000200060006930005002000013Q00049F012Q0020000100060B010700210001000600049F012Q002100012Q001E000700073Q0010563Q0005000700049F012Q002400010010563Q000500010030053Q000A000B0030053Q000C000B2Q007000036Q005E0103000100010006FC0002002C0001000100049F012Q002C00012Q0070000300014Q005E0103000100012Q00AA012Q00024Q0024012Q00013Q00023Q00023Q0003043Q00456E756D03073Q004B6579436F646500063Q0012DB3Q00013Q00206Q00024Q00019Q003Q00016Q00028Q00017Q00023Q0003043Q00456E756D030D3Q0055736572496E7075745479706500063Q0012DB3Q00013Q00206Q00024Q00019Q003Q00016Q00028Q00017Q00013Q0003073Q004B65794E616D6501043Q00201100013Q00012Q00562Q0100024Q003500016Q0024012Q00017Q00053Q0003073Q00696E6465784F6603043Q004D6F646503043Q0048656C64010003073Q00546F2Q676C656403134Q007E01035Q00202Q0003000300014Q000400016Q000500016Q00030005000200062Q000300080001000100049F012Q000800012Q00AA012Q00023Q0010563Q000200010030B83Q0003000400304Q000500044Q000300026Q00030001000100062Q000200110001000100049F012Q001100012Q0070000300034Q005E0103000100012Q00AA012Q00024Q0024012Q00017Q00053Q0003043Q004D61696403043Q004769766503073Q004368616E67656403073Q00436F2Q6E65637403083Q004765745374617465020E4Q007B01025Q00202Q00020002000100202Q00020002000200202Q00043Q000300202Q0004000400044Q000600016Q000400066Q00023Q00014Q000200013Q00202Q00033Q00052Q00F6000300044Q006101023Q00012Q00AA012Q00024Q0024012Q00017Q00043Q0003043Q004D61696403043Q004769766503073Q00436C69636B656403073Q00436F2Q6E656374020A4Q007000025Q00201001020002000100201100020002000200201001043Q00030020110004000400042Q0018010600014Q0072010400064Q006101023Q00012Q00AA012Q00024Q0024012Q00017Q00013Q00030B3Q0053657444697361626C656402064Q000801025Q00202Q0002000200014Q000400016Q0002000400016Q00028Q00017Q00063Q0003073Q005F756E62696E64002Q033Q004B657903043Q0042696E6403043Q004D61696403043Q004769766500204Q00707Q002010014Q00010006933Q000900013Q00049F012Q000900012Q00707Q002010014Q00012Q005E012Q000100012Q00707Q0030053Q000100022Q00707Q002010014Q00030026473Q000E0001000200049F012Q000E00012Q0024012Q00014Q00708Q0070000100013Q0020102Q01000100042Q007000025Q0020100102000200030006D400033Q000100032Q00708Q00703Q00024Q00703Q00034Q008C2Q01000300020010563Q000100012Q00703Q00043Q002010014Q00050020115Q00062Q007000025Q0020100102000200012Q004D012Q000200012Q0024012Q00013Q00013Q000A3Q0003053Q00626567616E03043Q004D6F646503063Q00546F2Q676C6503073Q00546F2Q676C656403043Q0048656C642Q0103063Q004F6E486F6C6403073Q00436C69636B656403043Q0046697265010001263Q0026473Q001B0001000100049F012Q001B00012Q007000015Q0020102Q01000100020026470001000C0001000300049F012Q000C00012Q007000016Q007000025Q0020100102000200042Q005F000200023Q00105600010004000200049F012Q000E00012Q007000015Q0030050001000500062Q007000015Q0020102Q0100010002002647000100160001000700049F012Q001600012Q007000015Q0020102Q01000100080020110001000100092Q00042Q01000200012Q0070000100014Q005E2Q01000100012Q0070000100024Q005E2Q010001000100049F012Q002500012Q007000015Q0020102Q0100010002002696000100250001000300049F012Q002500012Q007000015Q00300500010005000A2Q0070000100014Q005E2Q01000100012Q0070000100024Q005E2Q01000100012Q0024012Q00019Q002Q0003094Q007E00038Q00048Q000500016Q000600026Q0003000600014Q000300016Q0003000100016Q00028Q00017Q00063Q0003083Q0044697361626C656403093Q00436170747572696E672Q0103073Q004361707475726503043Q004D61696403043Q0047697665001B4Q00707Q002010014Q00010006FC3Q00080001000100049F012Q000800012Q00703Q00013Q002010014Q00020006933Q000900013Q00049F012Q000900012Q0024012Q00014Q00703Q00013Q0030053Q000200032Q00703Q00024Q005E012Q000100012Q001E8Q0070000100033Q0020102Q01000100040006D400023Q000100022Q00703Q00014Q00703Q00024Q00EF0001000200026Q00016Q00015Q00202Q00010001000500202Q0001000100064Q00038Q0001000300016Q00013Q00013Q00093Q0003093Q00436170747572696E67010003063Q0045736361706503093Q004261636B737061636503083Q0053657456616C7565030D3Q0055736572496E7075745479706503043Q00456E756D03083Q004B6579626F61726403073Q004B6579436F6465021E4Q007000025Q003005000200010002002647000100070001000300049F012Q000700012Q0070000200014Q005E0102000100012Q0024012Q00013Q0026470001000E0001000400049F012Q000E00012Q007000025Q0020110002000200052Q001E000400044Q004D0102000400012Q0024012Q00013Q00201001023Q0006001220010300073Q00201001030003000600201001030003000800066A010200190001000300049F012Q001900012Q007000025Q00201100020002000500201001043Q00092Q004D01020004000100049F012Q001D00012Q007000025Q00201100020002000500201001043Q00062Q004D0102000400012Q0024012Q00017Q002D3Q0003083Q0044697361626C65642Q033Q004E657703053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q003340026Q00184003163Q004261636B67726F756E645472616E73706172656E637903073Q0050612Q64696E67026Q00084003043Q004C69737403063Q00697061697273030A3Q005465787442752Q746F6E03043Q004E616D6503103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503043Q0054657874034Q00030B3Q004C61796F75744F7264657203063Q00506172656E7403063Q00436F726E657203083Q00506F736974696F6E030A3Q0066726F6D4F2Q66736574026Q001C40026Q002CC003053Q006C6F776572030A3Q0054657874436F6C6F723303043Q004D6F64652Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403093Q00636F6C6F722E6D6964030A3Q004D6F757365456E74657203073Q00436F2Q6E656374030A3Q004D6F7573654C6561766503113Q004D6F75736542752Q746F6E31436C69636B03043Q004F70656E03063Q0042752Q746F6E03053Q007769647468026Q00584003053Q00616C69676E03053Q007269676874008B4Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q0020085Q000200122Q000100036Q00023Q000200122Q000300053Q00202Q00030003000600122Q000400073Q00122Q000500083Q00122Q000600086Q000700026Q000700073Q00201F01070007000900206000070007000A2Q008C0103000700020010560002000400030030050002000B00072Q008C012Q000200022Q0070000100013Q0020102Q010001000C2Q001801025Q0012910003000D3Q0012910004000D3Q0012910005000D3Q0012910006000D4Q004D2Q01000600012Q0070000100013Q0020102Q010001000E2Q001801025Q001291000300084Q004D2Q01000300010012202Q01000F4Q0070000200024Q005E00010002000300049F012Q007F00012Q0070000600013Q00202E01060006000200122Q000700106Q00083Q000700102Q00080011000500122Q000900053Q00202Q00090009000600122Q000A00073Q00122Q000B00083Q00122Q000C00083Q00122Q000D00096Q0009000D000200102Q0008000400094Q000900013Q00202Q00090009001300122Q000A00146Q00090002000200102Q00080012000900302Q0008000B000700302Q00080015001600102Q00080017000400102Q000800186Q0006000800024Q000700013Q00202Q00070007001900122Q0008000D6Q000900066Q0007000900014Q000700013Q00202Q0007000700154Q00083Q000500122Q000900053Q00202Q00090009001B00122Q000A001C3Q00122Q000B00086Q0009000B000200102Q0008001A000900122Q000900053Q00202Q00090009000600122Q000A00073Q00122Q000B001D3Q00122Q000C00073Q00122Q000D00086Q0009000D000200102Q00080004000900202Q00090005001E4Q00090002000200102Q0008001500094Q000900033Q00202Q00090009002000062Q000500610001000900049F012Q006100012Q0070000900043Q002010010900090021001291000A00224Q00890009000200020006FC000900650001000100049F012Q006500012Q0070000900043Q002010010900090021001291000A00234Q00890009000200020010560008001F00090010560008001800062Q00890007000200020020100108000600240020110008000800250006D4000A3Q000100032Q00703Q00054Q0018012Q00064Q00703Q00044Q004D0108000A00010020100108000600260020110008000800250006D4000A0001000100022Q00703Q00054Q0018012Q00064Q004D0108000A00010020100108000600270020110008000800250006D4000A0002000100032Q00703Q00034Q0018012Q00054Q00703Q00064Q004D0108000A00012Q0018010800074Q00A801066Q00A801045Q000677000100270001000200049F012Q002700012Q0070000100063Q0020102Q01000100282Q0070000200033Q0020100102000200292Q001801036Q002A01043Q00020030050004002A002B0030050004002C002D2Q004D2Q01000400012Q0024012Q00013Q00033Q00043Q0003053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030E3Q00616C7068612E726F77486F766572000B4Q009D7Q00206Q00014Q000100016Q00023Q00014Q000300023Q00202Q00030003000300122Q000400046Q00030002000200102Q0002000200036Q000200012Q0024012Q00017Q00033Q0003053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F00074Q00AB016Q00206Q00014Q000100016Q00023Q000100302Q0002000200036Q000200016Q00017Q00023Q0003073Q005365744D6F646503053Q00436C6F736500084Q000A7Q00206Q00014Q000200018Q000200016Q00023Q00206Q00026Q000100016Q00017Q00063Q0003083Q0044697361626C656403053Q0054772Q656E03063Q0042752Q746F6E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030F3Q00616C7068612E77652Q6C486F76657200114Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002078014Q00024Q000100023Q00202Q0001000100034Q00023Q00014Q000300033Q00202Q00030003000500122Q000400066Q00030002000200102Q0002000400036Q000200016Q00017Q00053Q0003053Q0054772Q656E03063Q0042752Q746F6E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030A3Q00616C7068612E77652Q6C000C4Q0035016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q00014Q000300023Q00202Q00030003000400122Q000400056Q00030002000200102Q0002000300036Q000200016Q00017Q000C3Q0003073Q005F756E62696E6403063Q0069706169727303083Q00526567697374727903053Q007461626C6503063Q0072656D6F766503043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C03073Q00436C69636B6564030A3Q00556E726567697374657203043Q00466C616701243Q0020102Q013Q00010006930001000500013Q00049F012Q000500010020102Q013Q00012Q005E2Q01000100010012202Q0100024Q007000025Q0020100102000200032Q005E00010002000300049F012Q0013000100066A0105001300013Q00049F012Q00130001001220010600043Q00207C0006000600054Q00075Q00202Q0007000700034Q000800046Q00060008000100049F012Q001500010006770001000A0001000200049F012Q000A00012Q0070000100013Q00201400010001000600202Q0001000100074Q00010002000100202Q00013Q000800202Q0001000100094Q00010002000100202Q00013Q000A00202Q0001000100094Q0001000200014Q000100023Q0020102Q010001000B00201001023Q000C2Q00042Q01000200012Q0024012Q00017Q00043Q0003083Q005265676973747279026Q00F03F026Q00F0BF2Q000B4Q00707Q002010014Q00012Q00017Q001291000100023Q001291000200033Q0004F33Q000A00012Q007000045Q0020100104000400010020F90004000300040004513Q000600012Q0024012Q00017Q001B3Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C030A3Q00636F72652F466C61677303093Q00636F72652F5574696C030B3Q00636F72652F486F746B6579030E3Q006F7665726C6179732F4C6179657203043Q0067616D65030A3Q004765745365727669636503103Q0055736572496E7075745365727669636503073Q002Q5F696E646578026Q005A40025Q00806440030D3Q00436F6C6F7253657175656E63652Q033Q006E657703153Q00436F6C6F7253657175656E63654B6579706F696E74028Q0003063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F4002C3F5285C8FC2C53F021F85EB51B81ED53F026Q00E03F02713D0AD7A370E53F028FC2F5285C8FEA3F026Q00F03F017C4Q001A00015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q00122Q000900086Q00080002000200122Q000900093Q00202Q00090009000A00122Q000B000B6Q0009000B00024Q000A5Q00102Q000A000C000A00122Q000B000D3Q00122Q000C000E3Q00122Q000D000F3Q00202Q000D000D00104Q000E00063Q00122Q000F00113Q00202Q000F000F001000122Q001000123Q00122Q001100133Q00202Q00110011001400122Q001200153Q00122Q001300123Q00122Q001400126Q001100146Q000F3Q000200122Q001000113Q00202Q00100010001000122Q001100163Q00122Q001200133Q00202Q00120012001400122Q001300153Q00122Q001400153Q00122Q001500126Q001200156Q00103Q000200122Q001100113Q00202Q00110011001000122Q001200173Q00122Q001300133Q00202Q00130013001400122Q001400123Q00122Q001500153Q00122Q001600126Q001300166Q00113Q000200122Q001200113Q00202Q00120012001000122Q001300183Q00122Q001400133Q00202Q00140014001400122Q001500123Q00122Q001600153Q00122Q001700156Q001400176Q00123Q000200122Q001300113Q00202Q00130013001000122Q001400193Q00122Q001500133Q00202Q001500150014001291001600123Q001290001700123Q00122Q001800156Q001500186Q00133Q000200122Q001400113Q00202Q00140014001000122Q0015001A3Q00122Q001600133Q00202Q00160016001400122Q001700153Q00122Q001800123Q00122Q001900156Q001600196Q00143Q000200122Q001500113Q00202Q00150015001000122Q0016001B3Q00122Q001700133Q00202Q00170017001400122Q001800153Q00122Q001900123Q00122Q001A00126Q0017001A6Q00158Q000E3Q00012Q0089000D000200020006D4000E3Q0001000D2Q0018012Q000A4Q0018012Q00044Q0018012Q00064Q0018012Q00024Q0018012Q00014Q0018012Q00054Q0018012Q00094Q0018012Q00084Q0018012Q000B4Q0018012Q000D4Q0018012Q00074Q0018012Q000C4Q0018012Q00033Q001056000A0010000E2Q00AA010A00024Q0024012Q00013Q00013Q004F3Q00030C3Q007365746D6574617461626C6503043Q0054797065030B3Q00436F6C6F725069636B657203083Q00557365416C70686103053Q00416C7068612Q01030C3Q00416C70686144656661756C74026Q00F03F03083Q0043612Q6C6261636B03073Q004368616E6765642Q033Q006E657703083Q0047726F7570626F782Q033Q00526F7703063Q00412Q64526F7703043Q005465787403053Q005469746C6503063Q00636F6C6F757203073Q00542Q6F6C74697003073Q0044656661756C7403043Q007479706503063Q00737472696E67030A3Q00686578546F436F6C6F722Q033Q00476574030C3Q00636F6C6F722E612Q63656E742Q033Q004875652Q033Q005361742Q033Q0056616C03063Q00436F6C6F723303053Q00746F48535603063Q005377617463682Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574030B3Q0073697A652E73776174636803103Q004261636B67726F756E64436F6C6F723303163Q004261636B67726F756E645472616E73706172656E6379028Q00034Q00030B3Q004C61796F75744F72646572026Q00084003063Q00506172656E7403043Q00536C6F7403063Q00436F726E6572027Q0040030C3Q005377617463685374726F6B6503083Q0055495374726F6B6503053Q00436F6C6F7203073Q0066726F6D524742025Q00E06F40030C3Q005472616E73706172656E6379023D0AD7A3703DEA3F03093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203083Q00476574436F6C6F7203083Q0047657456616C756503063Q005F7061696E7403083Q0053657456616C75652Q033Q0053657403083Q00536574436F6C6F7203083Q00536574416C70686103063Q0047657448657803093Q004F6E4368616E676564030B3Q0053657444697361626C656403043Q004F70656E03043Q004D61696403043Q004769766503113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374030A3Q004D6F757365456E746572030A3Q004D6F7573654C6561766503073Q0044657374726F7903083Q0044697361626C656403083Q00526567697374657203063Q006F7074696F6E03DE3Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q005301048Q00058Q00030005000200302Q00030002000300202Q00040002000500262Q0004000D0001000600049F012Q000D00012Q001200046Q0065010400013Q0010560003000400040020100104000200070006FC000400130001000100049F012Q00130001001291000400083Q0010560003000500040020100104000200090010560003000900042Q0070000400013Q00201001040004000B2Q00F20004000100020010560003000A00040010560003000C3Q00201001040002000D0006FC0004002B0001000100049F012Q002B000100201100043Q000E2Q002A01063Q000200201001070002000F0006FC000700270001000100049F012Q002700010020100107000200100006FC000700270001000100049F012Q00270001001291000700113Q0010560006000F00070020100107000200120010560006001200072Q008C0104000600020010560003000D000400204701050002001300122Q000600146Q000700056Q00060002000200262Q000600370001001500049F012Q003700012Q0070000600023Q0020100106000600162Q0018010700054Q00890006000200022Q0018010500063Q0006FC0005003E0001000100049F012Q003E00012Q0070000600033Q002010010600060017001291000700184Q00890006000200022Q0018010500063Q0012200106001C3Q0020CF00060006001D4Q000700056Q00060002000800102Q0003001B000800102Q0003001A000700102Q0003001900064Q000600043Q00202Q00060006001F00122Q000700206Q00083Q000700300500080021001E001220010900233Q0020100109000900242Q0070000A00033Q002010010A000A0017001291000B00254Q0089000A000200022Q0070000B00033Q002010010B000B0017001291000C00254Q00F6000B000C4Q007301093Q00020010560008002200090010560008002600050030050008002700280030050008000F00290030050008002A002B00201001090004002D0010560008002C00092Q008C0106000800020010560003001E00062Q0070000600043Q00201001060006002E0012910007002F3Q00201001080003001E2Q004D0106000800012Q0070000600043Q00201001060006001F001291000700314Q002A01083Q00050012200109001C3Q00204300090009003300122Q000A00343Q00122Q000B00343Q00122Q000C00346Q0009000C0002001056000800320009003005000800350036003005000800370008001220010900393Q00201001090009003800201001090009003A00105600080038000900201001090003001E0010560008002C00092Q008C01060008000200105600030030000600029001065Q0010560003003B000600201001060003003B0010560003003C00060006D400060001000100012Q0018012Q00033Q0010560003003D00060006D400070002000100032Q0018012Q00064Q0018012Q00034Q00703Q00053Q0006D400080003000100032Q00703Q00024Q0018012Q00064Q0018012Q00073Q0010230103003E000800202Q00080003003E00102Q0003003F000800202Q00080003003E00102Q0003004000080006D400080004000100032Q00703Q00024Q0018012Q00064Q0018012Q00073Q0010560003004100080006D400080005000100012Q00703Q00023Q0010560003004200080006D400080006000100012Q0018012Q00043Q0010560003004300080006D400080007000100012Q0018012Q00043Q0010560003004400080006D400080008000100012Q00703Q00063Q0006D4000900090001000C2Q0018012Q00044Q00703Q00074Q00703Q00084Q00703Q00044Q00703Q00094Q00703Q00034Q0018012Q00074Q0018012Q00064Q0018012Q00084Q00703Q00024Q00703Q000A4Q00703Q000B3Q00105600030045000900200400090004004600202Q00090009004700202Q000B0003001E00202Q000B000B004800202Q000B000B00490006D4000D000A000100012Q0018012Q00034Q003C010B000D6Q00093Q000100202Q00090004004600202Q00090009004700202Q000B0003001E00202Q000B000B004A00202Q000B000B00490006D4000D000B000100042Q0018012Q00044Q00703Q000C4Q0018012Q00034Q00703Q00034Q003C010B000D6Q00093Q000100202Q00090004004600202Q00090009004700202Q000B0003001E00202Q000B000B004B00202Q000B000B00490006D4000D000C000100022Q00703Q000C4Q0018012Q00034Q0072010B000D4Q006101093Q00010006D40009000D000100032Q00703Q00074Q0018012Q00044Q00703Q00053Q0010810103004C00094Q000900066Q00090001000100202Q00090002004D00062Q000900D600013Q00049F012Q00D600010020110009000400442Q0065010B00014Q004D0109000B00012Q0070000900053Q00200200090009004E00122Q000A004F6Q000B00016Q000C00036Q0009000C00014Q000300028Q00013Q000E3Q00053Q0003063Q00436F6C6F723303073Q0066726F6D4853562Q033Q004875652Q033Q005361742Q033Q0056616C01083Q0012D0000100013Q00202Q00010001000200202Q00023Q000300202Q00033Q000400202Q00043Q00054Q000100046Q00019Q0000017Q00083Q0003063Q0053776174636803103Q004261636B67726F756E64436F6C6F723303083Q00476574436F6C6F7203163Q004261636B67726F756E645472616E73706172656E637903083Q00557365416C70686103053Q00416C706861026Q00F03F029Q00144Q00707Q002010014Q00012Q007000015Q0020110001000100032Q00890001000200020010563Q000200012Q00707Q002010014Q00012Q007000015Q0020102Q01000100050006930001001100013Q00049F012Q001100012Q007000015Q0020102Q01000100060010760001000700010006FC000100120001000100049F012Q00120001001291000100083Q0010563Q000400012Q0024012Q00017Q000A3Q0003083Q00476574436F6C6F7203083Q0043612Q6C6261636B03053Q007063612Q6C03053Q00416C70686103043Q007761726E03253Q005B4175726F72615D20636F6C6F727069636B65722063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q004368616E67656403043Q004669726503043Q00466C616700274Q001E019Q002Q000100016Q00013Q00206Q00016Q000200024Q000100013Q00202Q00010001000200062Q0001001900013Q00049F012Q001900010012202Q0100034Q00A6010200013Q00202Q0002000200024Q00038Q000400013Q00202Q0004000400044Q00010004000200062Q000100190001000100049F012Q00190001001220010300053Q001280000400063Q00122Q000500076Q000600026Q0005000200024Q0004000400054Q0003000200012Q0070000100013Q00205000010001000800202Q0001000100094Q00038Q000400013Q00202Q0004000400044Q0001000400014Q000100023Q00207C0001000100094Q000200013Q00202Q00020002000A4Q00038Q0001000300012Q0024012Q00017Q00093Q0003043Q007479706503063Q00737472696E67030A3Q00686578546F436F6C6F722Q033Q004875652Q033Q005361742Q033Q0056616C03063Q00436F6C6F723303053Q00746F48535603053Q005F73796E6303233Q001220010300014Q0018010400014Q00890003000200020026470003000A0001000200049F012Q000A00012Q007000035Q0020100103000300032Q0018010400014Q00890003000200022Q00182Q0100033Q0006FC0001000D0001000100049F012Q000D00012Q00AA012Q00023Q001220010300073Q0020100103000300082Q0018010400014Q005E0003000200050010563Q000600050010563Q000500040010563Q000400030006930002001900013Q00049F012Q001900012Q0070000300014Q005E01030001000100049F012Q001B00012Q0070000300024Q005E01030001000100201001033Q00090006930003002100013Q00049F012Q0021000100201001033Q00092Q0065010400014Q00040103000200012Q00AA012Q00024Q0024012Q00017Q00053Q0003053Q00416C70686103053Q00636C616D70026Q00F03F028Q0003053Q005F73796E6303184Q007000035Q00201001030003000200060B010400050001000100049F012Q00050001001291000400033Q001291000500043Q001291000600034Q008C0103000600020010563Q000100030006930002000E00013Q00049F012Q000E00012Q0070000300014Q005E01030001000100049F012Q001000012Q0070000300024Q005E01030001000100201001033Q00050006930003001600013Q00049F012Q0016000100201001033Q00052Q0065010400014Q00040103000200012Q00AA012Q00024Q0024012Q00017Q00023Q00030A3Q00636F6C6F72546F48657803083Q00476574436F6C6F7201074Q007000015Q0020102Q010001000100201100023Q00022Q00F6000200034Q00922Q016Q003500016Q0024012Q00017Q00063Q0003043Q004D61696403043Q004769766503073Q004368616E67656403073Q00436F2Q6E65637403083Q00476574436F6C6F7203053Q00416C706861020F4Q007B01025Q00202Q00020002000100202Q00020002000200202Q00043Q000300202Q0004000400044Q000600016Q000400066Q00023Q00014Q000200013Q00202Q00033Q00052Q008900030002000200201001043Q00062Q004D0102000400012Q00AA012Q00024Q0024012Q00017Q00013Q00030B3Q0053657444697361626C656402064Q000801025Q00202Q0002000200014Q000400016Q0002000400016Q00028Q00017Q00033Q00030A3Q00496E707574426567616E03073Q00436F2Q6E656374030A3Q00496E707574456E64656402174Q006501026Q001E000300033Q00201001043Q00010020110004000400020006D400063Q000100042Q0018012Q00024Q0018012Q00014Q0018012Q00034Q00708Q004D0104000600012Q007000045Q0020100104000400030020110004000400020006D400060001000100022Q0018012Q00024Q0018012Q00034Q008C0104000600020006D400050002000100032Q0018012Q00024Q0018012Q00034Q0018012Q00044Q00AA010500024Q0024012Q00013Q00033Q00073Q00030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F75636803083Q00506F736974696F6E030C3Q00496E7075744368616E67656403073Q00436F2Q6E656374011B3Q0020432Q013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000D0001000200049F012Q000D00010020102Q013Q0001001220010200023Q0020100102000200010020100102000200040006402Q01000D0001000200049F012Q000D00012Q0024012Q00014Q00652Q0100014Q009700018Q000100013Q00202Q00023Q00054Q0001000200014Q000100033Q00202Q00010001000600202Q0001000100070006D400033Q000100022Q00708Q00703Q00014Q008C2Q01000300022Q00952Q0100024Q0024012Q00013Q00013Q00053Q00030D3Q0055736572496E7075745479706503043Q00456E756D030D3Q004D6F7573654D6F76656D656E7403053Q00546F75636803083Q00506F736974696F6E01154Q007000015Q0006FC000100040001000100049F012Q000400012Q0024012Q00013Q0020102Q013Q0001001220010200023Q0020100102000200010020100102000200030006402Q0100110001000200049F012Q001100010020102Q013Q0001001220010200023Q0020100102000200010020100102000200040006402Q0100110001000200049F012Q001100012Q0024012Q00014Q0070000100013Q00201001023Q00052Q00042Q01000200012Q0024012Q00017Q00053Q00030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F756368030A3Q00446973636F2Q6E65637401173Q0020432Q013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000C0001000200049F012Q000C00010020102Q013Q0001001220010200023Q00201001020002000100201001020002000400066A2Q0100160001000200049F012Q001600012Q00652Q016Q00952Q016Q0070000100013Q0006930001001600013Q00049F012Q001600012Q0070000100013Q0020110001000100052Q00042Q01000200012Q001E000100014Q00952Q0100014Q0024012Q00017Q00013Q00030A3Q00446973636F2Q6E656374000C4Q0065017Q0095017Q00703Q00013Q0006933Q000800013Q00049F012Q000800012Q00703Q00013Q0020115Q00012Q0004012Q000200012Q00703Q00023Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00573Q0003083Q0044697361626C656403063Q0049734F70656E03063Q0053776174636803053Q00436C6F736503083Q00557365416C706861027Q0040026Q00F03F026Q002040026Q001C40026Q002240026Q0033402Q033Q004E657703053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577028Q0003163Q004261636B67726F756E645472616E73706172656E637903073Q0050612Q64696E6703043Q004E616D6503023Q00535603103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D4853562Q033Q0048756503063Q00506172656E7403063Q00436F726E6572026Q00084003093Q0066726F6D5363616C65030A3Q0055494772616469656E7403053Q00436F6C6F72030D3Q00436F6C6F7253657175656E6365030C3Q005472616E73706172656E6379030E3Q004E756D62657253657175656E636503163Q004E756D62657253657175656E63654B6579706F696E7403063Q005A496E64657803083Q00526F746174696F6E025Q00805640030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F030A3Q0066726F6D4F2Q66736574026Q001040025Q00388F4003083Q0055495374726F6B6503093Q00546869636B6E652Q73026Q00F83F030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F72646572030A3Q005465787442752Q746F6E03043Q0054657874034Q00026Q00144003083Q00506F736974696F6E026Q002640026Q00304003073Q0066726F6D524742026Q004140026Q00434003083Q00476574436F6C6F72030C3Q00536574412Q7472696275746503043Q0066692Q6C03053Q00546F6B656E030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E77652Q6C2Q033Q00476574030A3Q007261646975732E63746C026Q001840026Q0028C003013Q002303063Q00476574486578030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903103Q00436C656172546578744F6E466F637573010003043Q006D6F6E6F03073Q0054657874426F7803053Q005F73796E6303073Q00466F637573656403073Q00436F2Q6E65637403093Q00466F6375734C6F737403043Q004F70656E03053Q00776964746803053Q00616C69676E03053Q00726967687403073Q006F6E436C6F73650198023Q007000015Q0020102Q01000100010006930001000500013Q00049F012Q000500012Q0024012Q00014Q0070000100013Q0020102Q010001000200201001023Q00032Q00890001000200020006930001000F00013Q00049F012Q000F00012Q0070000100013Q0020102Q01000100042Q005E2Q01000100012Q0024012Q00013Q0020102Q013Q00050006930001001500013Q00049F012Q00150001001291000100063Q0006FC000100160001000100049F012Q00160001001291000100074Q0070000200023Q00104500020008000200202Q00020002000900202Q00030001000A4Q00020002000300202Q00030001000700202Q0003000300094Q00020002000300202Q00020002000900202Q00020002000B00202Q0002000200084Q000300033Q00202Q00030003000C00122Q0004000D6Q00053Q000200122Q0006000F3Q00202Q00060006001000122Q000700073Q00122Q000800113Q00122Q000900116Q000A00026Q0006000A000200102Q0005000E000600302Q0005001200074Q0003000500024Q000400033Q00202Q0004000400134Q000500033Q00122Q000600083Q00122Q000700083Q00122Q000800083Q00122Q000900086Q0004000900014Q000400033Q00202Q00040004000C00122Q0005000D6Q00063Q000500302Q00060014001500122Q0007000F3Q00202Q00070007001000122Q000800073Q00122Q000900113Q00122Q000A00116Q000B00026Q0007000B000200102Q0006000E000700122Q000700173Q00202Q00070007001800202Q00083Q001900122Q000900073Q00122Q000A00076Q0007000A000200102Q00060016000700302Q00060012001100102Q0006001A00034Q0004000600024Q000500033Q00202Q00050005001B00122Q0006001C6Q000700046Q0005000700014Q000500033Q00202Q00050005000C00122Q0006000D6Q00073Q000400122Q0008000F3Q00202Q00080008001D00122Q000900073Q00122Q000A00076Q0008000A000200102Q0007000E000800122Q000800173Q00202Q00080008001000122Q000900073Q00122Q000A00073Q00122Q000B00076Q0008000B000200102Q00070016000800302Q00070012001100102Q0007001A00044Q0005000700022Q0070000600033Q00201001060006001B0012910007001C4Q0018010800054Q004D0106000800012Q0070000600033Q00201001060006000C0012910007001E4Q002A01083Q0003001220010900203Q002010010900090010001220010A00173Q002010010A000A0010001291000B00073Q001291000C00073Q001291000D00074Q0072010A000D4Q007301093Q00020010560008001F0009001220010900223Q0020100109000900102Q002A010A00013Q001220010B00233Q002010010B000B0010001291000C00113Q001291000D00114Q008C010B000D0002001220010C00233Q002010010C000C0010001291000D00073Q001291000E00074Q0072010C000E4Q007A010A3Q00012Q00890009000200020010560008002100090010560008001A00052Q004D0106000800012Q0070000600033Q00201001060006000C0012DF0007000D6Q00083Q000500122Q0009000F3Q00202Q00090009001D00122Q000A00073Q00122Q000B00076Q0009000B000200102Q0008000E000900122Q000900173Q00202Q000900090010001291000A00113Q001291000B00113Q001291000C00114Q008C0109000C000200105600080016000900300500080012001100300500080024000600102B0108001A00044Q0006000800024Q000700033Q00202Q00070007001B00122Q0008001C6Q000900066Q0007000900014Q000700033Q00202Q00070007000C00122Q0008001E4Q002A01093Q0004001220010A00203Q002010010A000A0010001220010B00173Q002010010B000B0010001291000C00113Q001291000D00113Q001291000E00114Q0072010B000E4Q0073010A3Q00020010560009001F000A001220010A00223Q002010010A000A00102Q002A010B00013Q001220010C00233Q002010010C000C0010001291000D00113Q001291000E00074Q008C010C000E0002001220010D00233Q002010010D000D0010001291000E00073Q001291000F00114Q0072010D000F4Q007A010B3Q00012Q0089000A0002000200105600090021000A0030050009002500260010560009001A00062Q004D0107000900012Q0070000700033Q00201001070007000C0012DF0008000D6Q00093Q000500122Q000A00283Q00202Q000A000A001000122Q000B00293Q00122Q000C00296Q000A000C000200102Q00090027000A00122Q000A000F3Q00202Q000A000A002A001291000B000A3Q001291000C000A4Q008C010A000C00020010560009000E000A00300500090012000700300500090024002B00102B0109001A00044Q0007000900024Q000800033Q00202Q00080008001B00122Q0009002C6Q000A00076Q0008000A00014Q000800033Q00202Q00080008000C00122Q0009002D4Q002A010A3Q0004001220010B00173Q002043000B000B001000122Q000C00073Q00122Q000D00073Q00122Q000E00076Q000B000E0002001056000A001F000B003005000A002E002F001220010B00313Q002010010B000B0030002010010B000B0032001056000A0030000B001056000A001A00072Q004D0108000A00012Q0070000800033Q00201001080008000C001291000900334Q002A010A3Q0005001220010B000F3Q002010010B000B001D001291000C00073Q001291000D00074Q008C010B000D0002001056000A000E000B003005000A00120007003005000A00340035003005000A00240036001056000A001A00042Q008C0108000A00022Q0070000900033Q00201001090009000C001291000A000D4Q002A010B3Q0005001220010C000F3Q002010010C000C002A001291000D00114Q0070000E00023Q002060000E000E00092Q008C010C000E0002001056000B0037000C001220010C000F3Q002010010C000C0010001291000D00073Q001242010E00113Q00122Q000F00113Q00122Q0010000A6Q000C0010000200102Q000B000E000C00122Q000C00173Q00202Q000C000C001000122Q000D00073Q00122Q000E00073Q00122Q000F00074Q008C010C000F0002001056000B0016000C003005000B0012001100102B010B001A00034Q0009000B00024Q000A00033Q00202Q000A000A001B00122Q000B002C6Q000C00096Q000A000C00014Q000A00033Q00202Q000A000A000C00122Q000B001E4Q002A010C3Q00022Q0070000D00043Q001056000C001F000D001056000C001A00092Q004D010A000C00012Q0070000A00033Q002010010A000A000C0012DF000B000D6Q000C3Q000700122Q000D00283Q00202Q000D000D001000122Q000E00293Q00122Q000F00296Q000D000F000200102Q000C0027000D00122Q000D000F3Q00202Q000D000D0010001291000E00113Q0012D5000F00113Q00122Q001000293Q00122Q001100116Q000D0011000200102Q000C0037000D00122Q000D000F3Q00202Q000D000D002A00122Q000E001C3Q00122Q000F00386Q000D000F0002001056000C000E000D001220010D00173Q002043000D000D001000122Q000E00073Q00122Q000F00073Q00122Q001000076Q000D00100002001056000C0016000D003005000C00120011003005000C0024001C00102B010C001A00094Q000A000C00024Q000B00033Q00202Q000B000B001B00122Q000C00066Q000D000A6Q000B000D00014Q000B00033Q00202Q000B000B000C00122Q000C00334Q002A010D3Q0005001220010E000F3Q002010010E000E001D001291000F00073Q001291001000074Q008C010E00100002001056000D000E000E003005000D00120007003005000D00340035003005000D0024002B001056000D001A00092Q008C010B000D00022Q001E000C000F3Q00201001103Q0005000693001000FE2Q013Q00049F012Q00FE2Q012Q0070001000033Q00201001100010000C0012910011000D4Q002A01123Q00050012200113000F3Q00201001130013002A001291001400114Q0070001500023Q0020600015001500090020600015001500392Q008C0113001500020010560012003700130012200113000F3Q002010011300130010001291001400073Q001242011500113Q00122Q001600113Q00122Q0017000A6Q00130017000200102Q0012000E001300122Q001300173Q00202Q00130013003A00122Q0014003B3Q00122Q0015003B3Q00122Q0016003C4Q008C0113001600020010560012001600130030050012001200110010560012001A00032Q008C0110001200022Q0018010C00104Q0070001000033Q00201001100010001B0012910011002C4Q00180112000C4Q004D0110001200012Q0070001000033Q00201001100010000C0012910011000D4Q002A01123Q00040012200113000F3Q00201001130013001D001291001400073Q001291001500074Q008C0113001500020010560012000E001300201100133Q003D2Q008900130002000200105600120016001300300500120012001100102B0112001A000C4Q0010001200024Q001100033Q00202Q00110011001B00122Q0012002C6Q001300106Q0011001300014Q001100033Q00202Q00110011000C00122Q0012001E4Q002A01133Q0003001220011400203Q002010011400140010001220011500173Q002010011500150010001291001600073Q001291001700073Q001291001800074Q0072011500184Q007301143Q00020010560013001F0014001220011400223Q0020100114001400102Q002A011500013Q001220011600233Q002010011600160010001291001700113Q001291001800074Q008C011600180002001220011700233Q002010011700170010001291001800073Q001291001900114Q0072011700194Q007A01153Q00012Q00890014000200020010560013002100140010560013001A00102Q008C0111001300022Q0018010F00113Q0020110011000F003E0012910013003F4Q0065011400014Q004D0111001400012Q0018010F00104Q0070001100033Q00201001110011000C0012DF0012000D6Q00133Q000700122Q001400283Q00202Q00140014001000122Q001500293Q00122Q001600296Q00140016000200102Q00130027001400122Q0014000F3Q00202Q001400140010001291001500113Q0012D5001600113Q00122Q001700293Q00122Q001800116Q00140018000200102Q00130037001400122Q0014000F3Q00202Q00140014002A00122Q0015001C3Q00122Q001600386Q0014001600020010560013000E0014001220011400173Q00204300140014001000122Q001500073Q00122Q001600073Q00122Q001700076Q00140017000200105600130016001400300500130012001100300500130024001C0010560013001A000C2Q008C0111001300022Q0018010D00114Q0070001100033Q00201001110011001B001291001200064Q00180113000D4Q004D0111001300012Q0070001100033Q00201001110011000C001291001200334Q002A01133Q00050012200114000F3Q00201001140014001D001291001500073Q001291001600074Q008C0114001600020010560013000E001400300500130012000700300500130034003500300500130024002B0010560013001A000C2Q008C0111001300022Q0018010E00114Q0070001000023Q00206000100010000900201F01110001000A2Q009E01100010001100203E00110001000700201F0111001100092Q009E0110001000110020600010001000092Q0070001100033Q00201001110011000C0012910012000D4Q002A01133Q00050012200114000F3Q00201001140014002A001291001500114Q0018011600104Q008C01140016000200105600130037001400123F0114000F3Q00202Q00140014001000122Q001500073Q00122Q001600113Q00122Q001700113Q00122Q0018000B6Q00140018000200102Q0013000E00144Q001400033Q00202Q001400140040001291001500414Q00890014000200020010560013001600142Q0070001400033Q002010011400140040001291001500424Q00D600140002000200102Q00130012001400102Q0013001A00034Q0011001300024Q001200033Q00202Q00120012001B4Q001300053Q00202Q00130013004300122Q001400446Q0013000200022Q0018011400114Q004D0112001400012Q0070001200033Q0020100112001200342Q002A01133Q00060012200114000F3Q00201001140014002A001291001500453Q0012E5001600116Q00140016000200102Q00130037001400122Q0014000F3Q00202Q00140014001000122Q001500073Q00122Q001600463Q00122Q001700073Q00122Q001800116Q0014001800020010560013000E0014001291001400473Q00201100153Q00482Q00890015000200022Q006B0114001400150010560013003400142Q0070001400033Q0020100114001400400012910015004A4Q00890014000200020010560013004900140030050013004B004C0010560013001A00110012910014004D3Q0012910015004E4Q008C0112001500022Q006501135Q0006D400143Q0001000A2Q0018012Q00044Q0018017Q0018012Q00074Q0018012Q000A4Q0018012Q000F4Q0018012Q000D4Q0018012Q00134Q0018012Q00124Q00703Q00064Q00703Q00073Q0010563Q004F00142Q0070001500084Q0018011600083Q0006D400170001000100042Q0018012Q00044Q0018017Q00703Q00094Q0018012Q00144Q008C0115001700022Q0070001600084Q00180117000B3Q0006D400180002000100042Q0018012Q00094Q0018017Q00703Q00094Q0018012Q00144Q008C0116001800022Q001E001700173Q000693000E007502013Q00049F012Q007502012Q0070001800084Q00180119000E3Q0006D4001A0003000100042Q0018012Q000C4Q0018017Q00703Q00094Q0018012Q00144Q008C0118001A00022Q0018011700183Q0020100118001200500020110018001800510006D4001A0004000100022Q0018012Q00134Q00703Q000A4Q004D0118001A00010020100118001200520020110018001800510006D4001A0005000100062Q0018012Q00134Q00703Q000A4Q00703Q00094Q0018012Q00124Q0018017Q0018012Q00144Q004D0118001A00012Q0018011800144Q0065011900014Q00040118000200012Q0070001800013Q00201001180018005300201001193Q00032Q0018011A00034Q002A011B3Q00032Q0070001C000B3Q001056001B0054001C003005001B005500560006D4001C0006000100042Q0018012Q00154Q0018012Q00164Q0018012Q00174Q0018016Q001056001B0057001C2Q004D0118001B00012Q0024012Q00013Q00073Q00133Q0003103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D4853562Q033Q00487565026Q00F03F03083Q00506F736974696F6E03053Q005544696D3203093Q0066726F6D5363616C652Q033Q005361742Q033Q0056616C03083Q00476574436F6C6F7203163Q004261636B67726F756E645472616E73706172656E6379028Q002Q033Q006E6577026Q00E03F03053Q00416C70686103043Q005465787403013Q002303063Q0047657448657801484Q007000015Q001220010200023Q0020100102000200032Q0070000300013Q002010010300030004001291000400053Q001291000500054Q008C0102000500020010560001000100022Q0070000100023Q001220010200073Q0020100102000200082Q0070000300013Q0020100103000300092Q0070000400013Q00201001040004000A0010760004000500042Q008C0102000400020010560001000600022Q0070000100024Q0070000200013Q00201100020002000B2Q00890002000200020010560001000100022Q0070000100023Q0030050001000C000D2Q0070000100033Q001220010200073Q00201001020002000E2Q0070000300013Q00204300030003000400122Q0004000D3Q00122Q0005000F3Q00122Q0006000D6Q0002000600020010560001000600022Q0070000100043Q0006930001003600013Q00049F012Q003600012Q0070000100044Q00A3010200013Q00202Q00020002000B4Q00020002000200102Q0001000100024Q000100053Q00122Q000200073Q00202Q00020002000E4Q000300013Q00202Q00030003001000122Q0004000D3Q0012910005000F3Q0012910006000D4Q008C0102000600020010560001000600022Q0070000100063Q0006FC000100400001000100049F012Q004000012Q0070000100073Q001281000200126Q000300013Q00202Q0003000300134Q0003000200024Q00020002000300102Q0001001100020006FC3Q00450001000100049F012Q004500012Q0070000100084Q005E2Q010001000100049F012Q004700012Q0070000100094Q005E2Q01000100012Q0024012Q00017Q00093Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058028Q0003013Q00592Q033Q0053617403053Q00636C616D70026Q00F03F2Q033Q0056616C01274Q007000015Q0020102Q01000100012Q007000025Q0020100102000200020020100103000200030026460103000A0001000400049F012Q000A00010020100103000200050026EC0003000B0001000400049F012Q000B00012Q0024012Q00014Q0070000300014Q008A000400023Q00202Q00040004000700202Q00053Q000300202Q0006000100034Q00050005000600202Q0006000200034Q00050005000600122Q000600043Q00122Q000700086Q0004000700020010560003000600042Q0070000300014Q008A000400023Q00202Q00040004000700202Q00053Q000500202Q0006000100054Q00050005000600202Q0006000200054Q00050005000600122Q000600043Q00122Q000700086Q0004000700020010760004000800040010560003000900042Q0070000300034Q005E0103000100012Q0024012Q00017Q00073Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058028Q002Q033Q0048756503053Q00636C616D70026Q00F03F01174Q001500015Q00202Q0001000100014Q00025Q00202Q00020002000200202Q00030002000300262Q000300080001000400049F012Q000800012Q0024012Q00014Q0070000300014Q008A000400023Q00202Q00040004000600202Q00053Q000300202Q0006000100034Q00050005000600202Q0006000200034Q00050005000600122Q000600043Q00122Q000700076Q0004000700020010560003000500042Q0070000300034Q005E0103000100012Q0024012Q00017Q00073Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058028Q0003053Q00416C70686103053Q00636C616D70026Q00F03F01174Q001500015Q00202Q0001000100014Q00025Q00202Q00020002000200202Q00030002000300262Q000300080001000400049F012Q000800012Q0024012Q00014Q0070000300014Q008A000400023Q00202Q00040004000600202Q00053Q000300202Q0006000100034Q00050005000600202Q0006000200034Q00050005000600122Q000600043Q00122Q000700076Q0004000700020010560003000500042Q0070000300034Q005E0103000100012Q0024012Q00017Q00013Q00030D3Q0053657453752Q7072652Q73656400074Q0065012Q00014Q0095017Q00703Q00013Q002010014Q00012Q00652Q0100014Q0004012Q000200012Q0024012Q00017Q000A3Q00030D3Q0053657453752Q7072652Q736564030A3Q00686578546F436F6C6F7203043Q00546578742Q033Q004875652Q033Q005361742Q033Q0056616C03063Q00436F6C6F723303053Q00746F48535603013Q002303063Q0047657448657800224Q0065017Q0095017Q00703Q00013Q002010014Q00012Q00652Q016Q0004012Q000200012Q00703Q00023Q002010014Q00022Q0070000100033Q0020102Q01000100032Q00893Q000200020006933Q001A00013Q00049F012Q001A00012Q0070000100044Q003A000200046Q000300043Q00122Q000400073Q00202Q0004000400084Q00058Q00040002000600102Q00030006000600102Q00020005000500102Q0001000400044Q000100054Q005E2Q010001000100049F012Q002100012Q0070000100033Q001281000200096Q000300043Q00202Q00030003000A4Q0003000200024Q00020002000300102Q0001000300022Q0024012Q00017Q00023Q0003053Q005F73796E632Q000C4Q00708Q005E012Q000100012Q00703Q00014Q005E012Q000100012Q00703Q00023Q0006933Q000900013Q00049F012Q000900012Q00703Q00024Q005E012Q000100012Q00703Q00033Q0030053Q000100022Q0024012Q00017Q00013Q0003043Q004F70656E00044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00083Q0003083Q0044697361626C656403053Q0054772Q656E030C3Q005377617463685374726F6B6503053Q00436F6C6F722Q033Q00476574030C3Q00636F6C6F722E612Q63656E74030C3Q005472616E73706172656E6379029A5Q99C93F00124Q00707Q002010014Q00010006933Q000500013Q00049F012Q000500012Q0024012Q00014Q00703Q00013Q002010014Q00022Q0070000100023Q0020102Q01000100032Q002A01023Q00022Q0070000300033Q002010010300030005001291000400064Q00890003000200020010560002000400030030050002000700082Q004D012Q000200012Q0024012Q00017Q00083Q0003053Q0054772Q656E030C3Q005377617463685374726F6B6503053Q00436F6C6F7203063Q00436F6C6F72332Q033Q006E6577026Q00F03F030C3Q005472616E73706172656E6379023D0AD7A3703DEA3F000F4Q0054016Q00206Q00014Q000100013Q00202Q0001000100024Q00023Q000200122Q000300043Q00202Q00030003000500122Q000400063Q00122Q000500063Q00122Q000600066Q00030006000200102Q00020003000300302Q0002000700086Q000200016Q00017Q00093Q0003063Q0049734F70656E03063Q0053776174636803053Q00436C6F736503043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C030A3Q00556E726567697374657203043Q00466C616701154Q00AD2Q015Q00202Q00010001000100202Q00023Q00024Q00010002000200062Q0001000900013Q00049F012Q000900012Q007000015Q0020102Q01000100032Q005E2Q01000100012Q0070000100013Q0020102Q01000100040020110001000100052Q00042Q01000200010020102Q013Q00060020110001000100072Q00042Q01000200012Q0070000100023Q0020102Q010001000800201001023Q00092Q00042Q01000200012Q0024012Q00017Q00173Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C026Q00344003073Q005072696D61727903043Q0066692Q6C030C3Q00636F6C6F722E612Q63656E7403093Q0066692Q6C416C706861028Q0003043Q0074657874030E3Q00636F6C6F722E612Q63656E744F6E03063Q007374726F6B650003053Q0047686F7374030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E77652Q6C03083Q00636F6C6F722E686903063Q0044616E676572026Q00F03F030C3Q00636F6C6F722E64616E6765722Q033Q006E65772Q033Q00726F7701344Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q00890004000200022Q002A01055Q001291000600054Q002A01073Q00032Q002A01083Q000400308600080007000800302Q00080009000A00302Q0008000B000C00302Q0008000D000E00102Q0007000600084Q00083Q000400302Q00080007001000302Q00080009001100302Q0008000B001200302Q0008000D000E0010560007000F00082Q002A01083Q00040030050008000700100030050008000900140030050008000B00150030050008000D00150010560007001300080006D400083Q000100062Q0018012Q00074Q0018012Q00014Q0018012Q00064Q0018012Q00024Q0018012Q00044Q0018012Q00033Q0006D400090001000100032Q0018012Q00064Q0018012Q00014Q0018012Q00083Q0010560005001600090006D400090002000100032Q0018012Q00064Q0018012Q00014Q0018012Q00083Q0010560005001700092Q00AA010500024Q0024012Q00013Q00033Q00373Q0003073Q0056617269616E7403053Q0047686F737403043Q005465787403053Q005469746C6503063Q0062752Q746F6E2Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503063Q0042752Q746F6E03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q0003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E03043Q0066692Q6C03163Q004261636B67726F756E645472616E73706172656E637903043Q007479706503093Q0066692Q6C416C70686103063Q00737472696E67034Q00030B3Q004C61796F75744F7264657203063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03063Q007374726F6B6503083Q0055495374726F6B6503053Q00436F6C6F72030C3Q005472616E73706172656E6379029A5Q99E13F03093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F7264657203093Q0066726F6D5363616C65030A3Q0054657874436F6C6F723303043Q0074657874030E3Q005465787458416C69676E6D656E7403063Q0043656E74657203043Q005479706503083Q00496E7374616E636503053Q004C6162656C03073Q00436C69636B656403063Q005F61726D6564010003093Q005F6261736554657874030A3Q004D6F757365456E74657203073Q00436F2Q6E656374030A3Q004D6F7573654C6561766503113Q004D6F75736542752Q746F6E31436C69636B03073Q0053657454657874030B3Q0053657444697361626C656403073Q0044657374726F7903A74Q007000035Q0020100104000100012Q00160103000300040006FC000300070001000100049F012Q000700012Q007000035Q0020100103000300020020100104000100030006FC0004000E0001000100049F012Q000E00010020100104000100040006FC0004000E0001000100049F012Q000E0001001291000400054Q0070000500013Q002010010500050006001291000600074Q002A01073Q00070030050007000800090012200108000B3Q00201001080008000C0012910009000D3Q001291000A000E3Q001291000B000E4Q0070000C00024Q008C0108000C00020010560007000A00082Q0070000800013Q0020100108000800100020100109000300112Q008900080002000200109E0007000F000800122Q000800133Q00202Q0009000300144Q00080002000200262Q0008002B0001001500049F012Q002B00012Q0070000800013Q0020100108000800100020100109000300142Q00890008000200020006FC0008002C0001000100049F012Q002C000100201001080003001400105600070012000800300500070003001600060B010800310001000200049F012Q003100010012910008000D3Q001056000700170008001056000700184Q008C0105000700022Q0070000600013Q0020100106000600192Q0070000700033Q00201001070007001A0012910008001B4Q00890007000200022Q0018010800054Q004D0106000800012Q001E000600063Q00201001070003001C0006930007005200013Q00049F012Q005200012Q0070000700013Q0020100107000700060012910008001D4Q002A01093Q00052Q0070000A00033Q002010010A000A001A002010010B0003001C2Q0089000A000200020010560009001E000A0030050009001F002000300500090021000D001220010A00233Q0020E9000A000A002200202Q000A000A002400102Q00090022000A00102Q0009001800054Q0007000900024Q000600074Q0070000700013Q0020100107000700032Q002A01083Q00050012200109000B3Q002010010900090025001291000A000D3Q001291000B000D4Q008C0109000B00020010560008000A00090010560008000300042Q0070000900013Q002010010900090010002010010A000300272Q0089000900020002001056000800260009001220010900233Q0020100109000900280020100109000900290010560008002800090010560008001800052Q00890007000200022Q002A01083Q00070030050008002A00090010560008002B00050010560008002C00072Q0070000900043Q00201001090009000C2Q00F20009000100020010560008002D00090020100109000100010006FC000900730001000100049F012Q00730001001291000900023Q0010560008000100090030050008002E002F0010560008003000040006D400093Q000100022Q0018012Q00084Q00703Q00033Q0006D4000A0001000100022Q0018012Q00084Q00703Q00033Q002010010B00050031002011000B000B00320006D4000D0002000100052Q0018012Q00054Q0018012Q00084Q00703Q00054Q00703Q00034Q0018012Q000A4Q004D010B000D0001002010010B00050033002011000B000B00320006D4000D0003000100052Q0018012Q00084Q00703Q00054Q0018012Q00054Q00703Q00034Q0018012Q00094Q004D010B000D00012Q001E000B000B3Q002010010C00050034002011000C000C00320006D4000E0004000100082Q0018012Q00054Q0018012Q00014Q0018012Q00084Q0018012Q000B4Q0018012Q00074Q00703Q00034Q0018012Q00064Q0018012Q00034Q004D010C000E00010006D4000C0005000100012Q0018012Q00073Q00105600080035000C0006D4000C0006000100022Q0018012Q00054Q0018012Q00073Q00105600080036000C0006D4000C0007000100012Q0018012Q00053Q00105600080037000C2Q00AA010800024Q0024012Q00013Q00083Q00073Q0003073Q0056617269616E7403073Q005072696D617279028Q0003063Q0044616E676572026Q00F03F2Q033Q00476574030A3Q00616C7068612E77652Q6C00124Q00707Q002010014Q00010026473Q00060001000200049F012Q000600010012913Q00034Q00AA012Q00024Q00707Q002010014Q00010026473Q000C0001000400049F012Q000C00010012913Q00054Q00AA012Q00024Q00703Q00013Q0020BB5Q000600122Q000100078Q00019Q008Q00017Q00073Q0003073Q0056617269616E7403073Q005072696D617279028Q0003063Q0044616E67657202295C8FC2F528EC3F2Q033Q00476574030F3Q00616C7068612E77652Q6C486F76657200124Q00707Q002010014Q00010026473Q00060001000200049F012Q000600010012913Q00034Q00AA012Q00024Q00707Q002010014Q00010026473Q000C0001000400049F012Q000C00010012913Q00054Q00AA012Q00024Q00703Q00013Q0020BB5Q000600122Q000100078Q00019Q008Q00017Q00083Q0003063Q0041637469766503073Q0056617269616E7403073Q005072696D61727903053Q0054772Q656E03103Q004261636B67726F756E64436F6C6F72332Q033Q00476574030F3Q00636F6C6F722E612Q63656E7444696D03163Q004261636B67726F756E645472616E73706172656E6379001D4Q00707Q002010014Q00010006FC3Q00050001000100049F012Q000500012Q0024012Q00014Q00703Q00013Q002010014Q00020026473Q00140001000300049F012Q001400012Q00703Q00023Q00209C5Q00044Q00018Q00023Q00014Q000300033Q00202Q00030003000600122Q000400076Q00030002000200102Q0002000500036Q0002000100044Q001C00012Q00703Q00023Q002010014Q00042Q007000016Q002A01023Q00012Q0070000300044Q00F20003000100020010560002000800032Q004D012Q000200012Q0024012Q00017Q00073Q0003073Q0056617269616E7403073Q005072696D61727903053Q0054772Q656E03103Q004261636B67726F756E64436F6C6F72332Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403163Q004261636B67726F756E645472616E73706172656E637900184Q00707Q002010014Q00010026473Q000F0001000200049F012Q000F00012Q00703Q00013Q00209C5Q00034Q000100026Q00023Q00014Q000300033Q00202Q00030003000500122Q000400066Q00030002000200102Q0002000400036Q0002000100044Q001700012Q00703Q00013Q002010014Q00032Q0070000100024Q002A01023Q00012Q0070000300044Q00F20003000100020010560002000700032Q004D012Q000200012Q0024012Q00017Q001A3Q0003063Q0041637469766503073Q00436F6E6669726D03063Q005F61726D65642Q0103043Q007469636B027Q004003043Q005465787403053Q00737572653F030A3Q0054657874436F6C6F72332Q033Q00476574030C3Q00636F6C6F722E64616E676572030C3Q005472616E73706172656E6379028Q0003043Q007461736B03053Q0064656C6179010003093Q005F626173655465787403043Q0074657874029A5Q99E13F03083Q0043612Q6C6261636B03053Q007063612Q6C03043Q007761726E03203Q005B4175726F72615D2062752Q746F6E2063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q00436C69636B656403043Q004669726500564Q00707Q002010014Q00010006FC3Q00050001000100049F012Q000500012Q0024012Q00014Q00703Q00013Q002010014Q00020006933Q002C00013Q00049F012Q002C00012Q00703Q00023Q002010014Q00030006FC3Q002C0001000100049F012Q002C00012Q00703Q00023Q0030053Q00030004001220012Q00054Q00F23Q000100020020605Q00062Q0095012Q00034Q00703Q00043Q0030053Q000700082Q00703Q00044Q0070000100053Q0020102Q010001000A0012910002000B4Q00890001000200020010563Q000900012Q00703Q00063Q0006933Q002000013Q00049F012Q002000012Q00703Q00063Q0030053Q000C000D001220012Q000E3Q002010014Q000F001291000100063Q0006D400023Q000100062Q00703Q00024Q00703Q00034Q00703Q00044Q00703Q00054Q00703Q00074Q00703Q00064Q004D012Q000200012Q0024012Q00014Q00703Q00023Q0030053Q000300102Q001E8Q0095012Q00034Q00703Q00044Q0070000100023Q0020102Q01000100110010563Q000700012Q00703Q00044Q0070000100053Q0020102Q010001000A2Q0070000200073Q0020100102000200122Q00890001000200020010563Q000900012Q00703Q00063Q0006933Q004000013Q00049F012Q004000012Q00703Q00063Q0030053Q000C00132Q00703Q00013Q002010014Q00140006933Q005100013Q00049F012Q00510001001220012Q00154Q0070000100013Q0020102Q01000100142Q005E3Q000200010006FC3Q00510001000100049F012Q00510001001220010200163Q001280000300173Q00122Q000400186Q000500016Q0004000200024Q0003000300044Q0002000200012Q00703Q00023Q002010014Q00190020115Q001A2Q0004012Q000200012Q0024012Q00013Q00013Q000B3Q0003063Q005F61726D656403043Q007469636B027B14AE47E17A843F010003043Q005465787403093Q005F6261736554657874030A3Q0054657874436F6C6F72332Q033Q0047657403043Q0074657874030C3Q005472616E73706172656E6379029A5Q99E13F00204Q00707Q002010014Q00010006933Q001F00013Q00049F012Q001F00012Q00703Q00013Q0006933Q001F00013Q00049F012Q001F0001001220012Q00024Q00F23Q000100022Q0070000100013Q00203E0001000100030006D70001001F00013Q00049F012Q001F00012Q00707Q00309B012Q000100046Q00026Q00015Q00202Q00010001000600104Q000500016Q00026Q000100033Q00202Q0001000100084Q000200043Q00202Q0002000200094Q00010002000200104Q000700016Q00053Q00064Q001F00013Q00049F012Q001F00012Q00703Q00053Q0030053Q000A000B2Q0024012Q00017Q00033Q0003093Q005F626173655465787403063Q005F61726D656403043Q005465787402083Q0010563Q0001000100201001023Q00020006FC000200060001000100049F012Q000600012Q007000025Q0010560002000300012Q00AA012Q00024Q0024012Q00017Q00043Q0003063Q0041637469766503103Q00546578745472616E73706172656E6379029A5Q99E13F028Q00020D4Q002F00028Q000300013Q00102Q0002000100034Q000200013Q00062Q0001000900013Q00049F012Q00090001001291000300033Q0006FC0003000A0001000100049F012Q000A0001001291000300043Q0010560002000200032Q00AA012Q00024Q0024012Q00017Q00033Q0003073Q00436C69636B6564030D3Q00446973636F2Q6E656374412Q6C03073Q0044657374726F7901073Q0020102Q013Q00010020110001000100022Q00042Q01000200012Q007000015Q0020110001000100032Q00042Q01000200012Q0024012Q00017Q001B3Q0003063Q00412Q64526F7703063Q00486569676874026Q00104003073Q00542Q6F6C74697003043Q005465787403063Q0062752Q746F6E2Q033Q004E657703053Q004672616D6503043Q004E616D65030C3Q0042752Q746F6E486F6C646572030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F03083Q00506F736974696F6E03053Q005544696D3203093Q0066726F6D5363616C6503043Q0053697A65026Q00F03F028Q0003163Q004261636B67726F756E645472616E73706172656E637903063Q00506172656E7403043Q00522Q6F742Q033Q00526F7703073Q00456C656D656E7403043Q004D61696403043Q0047697665023B3Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q00201100023Q00012Q002A01043Q00022Q007000055Q0020600005000500030010560004000200050020100105000100040010560004000400052Q008C0102000400020020100103000100050006FC000300100001000100049F012Q00100001001291000300063Q0010560002000500032Q00FF000300013Q00202Q00030003000700122Q000400086Q00053Q000600302Q00050009000A00122Q0006000C3Q00202Q00060006000D00122Q0007000E3Q00122Q0008000E6Q00060008000200102Q0005000B000600122Q000600103Q00202Q00060006001100122Q0007000E3Q00122Q0008000E6Q00060008000200102Q0005000F000600122Q000600103Q00202Q00060006000D00122Q000700133Q00122Q000800143Q00122Q000900146Q000A8Q0006000A000200102Q00050012000600302Q00050015001300202Q00060002001700102Q0005001600064Q0003000500024Q000400026Q000500036Q000600013Q00122Q000700136Q00040007000200102Q00040018000200102Q00020019000400202Q00050002001A00202Q00050005001B4Q000700046Q0005000700014Q000400028Q00017Q00273Q0003063Q00412Q64526F7703063Q00486569676874026Q00104003043Q0054657874034Q002Q033Q004E657703053Q004672616D6503043Q004E616D6503093Q0042752Q746F6E526F77030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F03083Q00506F736974696F6E03053Q005544696D3203093Q0066726F6D5363616C6503043Q0053697A65026Q00F03F028Q0003163Q004261636B67726F756E645472616E73706172656E637903063Q00506172656E7403043Q00522Q6F74030C3Q0055494C6973744C61796F7574030D3Q0046692Q6C446972656374696F6E03043Q00456E756D030A3Q00486F72697A6F6E74616C03073Q0050612Q64696E6703043Q005544696D03093Q00536F72744F72646572030B3Q004C61796F75744F7264657203063Q0069706169727303083Q00496E7374616E6365026Q0010C003043Q004D61696403043Q004769766503053Q007461626C6503063Q00636F6E63617403013Q002003073Q00456C656D656E74026E3Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q00201100023Q00012Q007D00043Q00014Q00055Q00202Q00050005000300102Q0004000200054Q00020004000200302Q0002000400054Q000300013Q00202Q00030003000600122Q000400076Q00053Q000600302Q00050008000900122Q0006000B3Q00202Q00060006000C00122Q0007000D3Q00122Q0008000D6Q00060008000200102Q0005000A000600122Q0006000F3Q00202Q00060006001000122Q0007000D3Q00122Q0008000D6Q00060008000200102Q0005000E000600122Q0006000F3Q00202Q00060006000C00122Q000700123Q00122Q000800133Q00122Q000900136Q000A8Q0006000A000200102Q00050011000600302Q00050014001200202Q00060002001600102Q0005001500064Q0003000500024Q000400013Q00202Q00040004000600122Q000500176Q00063Q000400122Q000700193Q00202Q00070007001800202Q00070007001A00102Q00060018000700122Q0007001C3Q00202Q00070007000C00122Q000800133Q00122Q000900036Q00070009000200102Q0006001B000700122Q000700193Q00202Q00070007001D00202Q00070007001E00102Q0006001D000700102Q0006001500034Q0004000600014Q00048Q00055Q00122Q0006001F6Q000700016Q00060002000800044Q006300012Q0070000B00024Q0018010C00034Q0018010D000A4Q0018010E00094Q008C010B000E0002002010010C000B0020001220010D000F3Q002010010D000D000C2Q0001000E00013Q001003010E0012000E2Q0001000F00013Q00203E000F000F001200107D010F0021000F2Q0001001000014Q00CC000F000F0010001291001000134Q007000116Q008C010D00110002001056000C0011000D2Q0001000C00043Q002060000C000C00122Q004A0104000C000B2Q0001000C00053Q002060000C000C0012002010010D000A00040006FC000D005E0001000100049F012Q005E0001001291000D00054Q004A0105000C000D002010010C00020022002011000C000C00232Q0018010E000B4Q004D010C000E0001000677000600420001000200049F012Q00420001001220010600243Q0020100106000600252Q0018010700053Q001291000800264Q008C0106000800020010560002000400060010560002002700042Q00AA010400024Q0024012Q00017Q00093Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F5369676E616C030A3Q00636F72652F466C616773030A3Q00636F72652F476C797068030B3Q00636F72652F486F746B657903073Q002Q5F696E6465782Q033Q006E657701234Q006500015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q00102Q0008000800080006D400093Q000100082Q0018012Q00084Q0018012Q00044Q0018012Q00014Q0018012Q00024Q0018012Q00064Q0018012Q00054Q0018012Q00074Q0018012Q00033Q0010560008000900092Q00AA010800024Q0024012Q00013Q00013Q00623Q00030C3Q007365746D6574617461626C6503043Q005479706503053Q00496E70757403073Q004E756D657269632Q0103093Q004D61784C656E677468030C3Q0046696E69736865644F6E6C7903083Q0046696E697368656403083Q0043612Q6C6261636B03073Q004368616E6765642Q033Q006E657703083Q0047726F7570626F7803063Q00412Q64526F7703043Q005465787403053Q005469746C6503073Q00542Q6F6C7469702Q033Q00526F7703073Q00456C656D656E7403053Q005769647468026Q005A4003053Q004669656C642Q033Q004E657703053Q004672616D6503043Q004E616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q00314003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030A3Q00616C7068612E77652Q6C030B3Q004C61796F75744F72646572026Q00F03F03063Q00506172656E7403043Q00536C6F7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03063Q005374726F6B6503083Q0055495374726F6B6503053Q00436F6C6F72030C3Q00636F6C6F722E612Q63656E74030C3Q005472616E73706172656E637903093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503043Q00456E756D03063Q00426F726465722Q033Q00426F7803083Q00506F736974696F6E026Q001840028Q00026Q0036C003073Q0044656661756C74034Q00030F3Q00506C616365686F6C64657254657874030B3Q00506C616365686F6C64657203113Q00506C616365686F6C646572436F6C6F723303083Q00636F6C6F722E6C6F030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903103Q00436C656172546578744F6E466F6375730100030C3Q00546578745472756E6361746503053Q004174456E6403043Q006D6F6E6F03023Q00756903073Q0054657874426F7803053Q00436C656172030A3Q005465787442752Q746F6E030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F026Q0014C0026Q00264003073Q0056697369626C6503053Q0043726F2Q73026Q00224003093Q0066726F6D5363616C6503053Q0056616C756503043Q004D61696403043Q004769766503183Q0047657450726F70657274794368616E6765645369676E616C03073Q00436F2Q6E65637403073Q00466F637573656403093Q00466F6375734C6F737403113Q004D6F75736542752Q746F6E31436C69636B03083Q0053657456616C75652Q033Q0053657403083Q0047657456616C756503093Q004765744E756D62657203093Q004F6E4368616E676564030B3Q0053657444697361626C656403073Q0044657374726F7903083Q0044697361626C656403083Q00526567697374657203063Q006F7074696F6E032B012Q0006FC000200040001000100049F012Q000400012Q002A01036Q0018010200033Q001220010300014Q005301048Q00058Q00030005000200302Q00030002000300202Q00040002000400262Q0004000D0001000500049F012Q000D00012Q001200046Q0065010400013Q001056000300040004002010010400020006001056000300060004002010010400020008002696000400150001000500049F012Q001500012Q001200046Q0065010400013Q0010560003000700040020100104000200090010560003000900042Q0070000400013Q00201001040004000B2Q00F20004000100020010560003000A00040010560003000C3Q00201100043Q000D2Q002A01063Q000200201001070002000E0006FC000700240001000100049F012Q0024000100201001070002000F0010560006000E000700203E01070002001000102Q0006001000074Q00040006000200102Q00030011000400102Q00040012000300202Q00050002001300062Q0005002E0001000100049F012Q002E0001001291000500144Q0070000600023Q00208201060006001600122Q000700176Q00083Q000600302Q00080018000300122Q0009001A3Q00202Q00090009001B4Q000A00053Q00122Q000B001C6Q0009000B000200102Q0008001900092Q0070000900023Q00203C00090009001E00122Q000A001F6Q00090002000200102Q0008001D00094Q000900023Q00202Q00090009001E00122Q000A00216Q00090002000200102Q00080020000900302Q0008002200230020100109000400250010560008002400092Q008C0106000800020010560003001500062Q0070000600023Q0020100106000600262Q0070000700033Q002010010700070027001291000800284Q00890007000200020020100108000300152Q004D0106000800012Q00E3000600023Q00202Q00060006001600122Q0007002A6Q00083Q00054Q000900033Q00202Q00090009002700122Q000A002C6Q00090002000200102Q0008002B000900302Q0008002D00230030050008002E0023001220010900303Q00201001090009002F0020100109000900310010560008002F00090020100109000300150010560008002400092Q008C0106000800020010560003002900062Q0070000600023Q00201001060006000E2Q002A01073Q000A0030B300070018003200122Q0008001A3Q00202Q00080008001B00122Q000900343Q00122Q000A00356Q0008000A000200102Q00070033000800122Q0008001A3Q00202Q00080008000B00122Q000900233Q001291000A00363Q001291000B00233Q001291000C00354Q008C0108000C00020010560007001900080020100108000200370006FC000800790001000100049F012Q00790001001291000800383Q0010560007000E000800201001080002003A0006FC0008007E0001000100049F012Q007E0001001291000800383Q0010560007003900082Q0070000800033Q00203C00080008002700122Q0009003C6Q00080002000200102Q0007003B00084Q000800023Q00202Q00080008001E00122Q0009003E6Q00080002000200102Q0007003D000800302Q0007003F0040001220010800303Q0020100108000800410020100108000800420010560007004100080020100108000300150010560007002400080020100108000300040006930008009600013Q00049F012Q00960001001291000800433Q0006FC000800970001000100049F012Q00970001001291000800443Q001291000900454Q008C0106000900020010560003003200062Q006B000600023Q00202Q00060006001600122Q000700476Q00083Q000800302Q00080018004600122Q000900493Q00202Q00090009000B00122Q000A00233Q00122Q000B004A6Q0009000B00020010560008004800090012200109001A3Q00201001090009000B001291000A00233Q0012D5000B004B3Q00122Q000C004A3Q00122Q000D00356Q0009000D000200102Q00080033000900122Q0009001A3Q00202Q00090009001B00122Q000A004C3Q00122Q000B004C6Q0009000B00020010560008001900090030050008002000230030050008000E00380030050008004D00400020100109000300150010560008002400092Q008C0106000800020010560003004600062Q0070000600043Q00201001060006004E0020100107000300460012910008004F3Q0012910009003C4Q008C010600090002001220010700493Q00203D01070007000B00122Q0008004A3Q00122Q0009004A6Q00070009000200102Q00060048000700122Q0007001A3Q00202Q00070007005000122Q0008004A3Q00122Q0009004A6Q00070009000200105600060033000700201001070003003200201001070007000E0010560003005100070006D400073Q000100012Q0018012Q00033Q0006D400080001000100022Q0018012Q00034Q00703Q00054Q006501095Q0006D4000A0002000100032Q0018012Q00094Q0018012Q00034Q0018012Q00073Q002010010B00040052002063000B000B005300202Q000D0003003200202Q000D000D005400122Q000F000E6Q000D000F000200202Q000D000D00550006D4000F0003000100032Q0018012Q000A4Q0018012Q00034Q0018012Q00084Q003C010D000F6Q000B3Q000100202Q000B0004005200202Q000B000B005300202Q000D0003003200202Q000D000D005600202Q000D000D00550006D4000F0004000100032Q00703Q00064Q00703Q00074Q0018012Q00034Q003C010D000F6Q000B3Q000100202Q000B0004005200202Q000B000B005300202Q000D0003003200202Q000D000D005700202Q000D000D00550006D4000F0005000100052Q00703Q00064Q00703Q00074Q0018012Q00034Q0018012Q00084Q0018012Q00024Q003C010D000F6Q000B3Q000100202Q000B0004005200202Q000B000B005300202Q000D0003004600202Q000D000D005800202Q000D000D00550006D4000F0006000100012Q0018012Q00034Q0072010D000F4Q0061010B3Q00010006D4000B0007000100022Q0018012Q00074Q0018012Q00083Q00105600030059000B002010010B000300590010560003005A000B000290010B00083Q0010560003005B000B000290010B00093Q0010560003005C000B0006D4000B000A000100012Q0018012Q00043Q0010560003005D000B0006D4000B000B000100012Q0018012Q00043Q0010560003005E000B0006D4000B000C000100022Q0018012Q00044Q00703Q00053Q0010810103005F000B4Q000B00076Q000B0001000100202Q000B0002006000062Q000B00232Q013Q00049F012Q00232Q01002011000B0003005E2Q0065010D00014Q004D010B000D00012Q0070000B00053Q002002000B000B006100122Q000C00626Q000D00016Q000E00036Q000B000E00014Q000300028Q00013Q000D3Q00053Q0003053Q00436C65617203073Q0056697369626C652Q033Q00426F7803043Q0054657874029Q000C4Q00707Q002010014Q00012Q007000015Q0020102Q01000100030020102Q01000100042Q0001000100013Q000E0F000500090001000100049F012Q000900012Q001200016Q00652Q0100013Q0010563Q000200012Q0024012Q00017Q00093Q0003083Q0043612Q6C6261636B03053Q007063612Q6C03053Q0056616C756503043Q007761726E031F3Q005B4175726F72615D20696E7075742063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6703073Q004368616E67656403043Q004669726503043Q00466C616700214Q00707Q002010014Q00010006933Q001300013Q00049F012Q00130001001220012Q00024Q00582Q015Q00202Q0001000100014Q00025Q00202Q0002000200036Q0002000100064Q00130001000100049F012Q00130001001220010200043Q001280000300053Q00122Q000400066Q000500016Q0004000200024Q0003000300044Q0002000200012Q00707Q002010014Q00070020115Q00082Q007000025Q0020100102000200032Q004D012Q000200012Q00703Q00013Q002010014Q00082Q007000015Q0020102Q01000100092Q007000025Q0020100102000200032Q004D012Q000200012Q0024012Q00017Q00103Q002Q033Q00426F7803043Q005465787403073Q004E756D6572696303043Q006773756203093Q005B5E2564252E252D5D034Q002Q033Q00737562026Q00F03F03013Q002D03023Q00252D03053Q006D6174636803113Q005E285B5E252E5D2A29252E3F282E2A292403023Q00252E03043Q0066696E6403013Q002E03093Q004D61784C656E67746800554Q00707Q0006933Q000400013Q00049F012Q000400012Q0024012Q00014Q0065012Q00014Q0095017Q00703Q00013Q002010014Q0001002010014Q00022Q0070000100013Q0020102Q01000100030006930001003900013Q00049F012Q0039000100201100013Q00040012EB000300053Q00122Q000400066Q0001000400026Q00013Q00202Q00013Q000700122Q000300083Q00122Q000400086Q00010004000200262Q000100190001000900049F012Q001900012Q001200016Q00652Q0100013Q00201100023Q00040012910004000A3Q001291000500064Q008C0102000500022Q0018012Q00023Q00201100023Q000B0012910004000C4Q00270002000400030020110004000300040012910006000D3Q001291000700064Q008C0104000700022Q0018010300044Q0018010400023Q00201100053Q000E0012910007000D4Q008C0105000700020006930005003200013Q00049F012Q003200010012910005000F4Q0018010600034Q006B0105000500060006FC000500330001000100049F012Q00330001001291000500064Q006B012Q000400050006930001003900013Q00049F012Q00390001001291000400094Q001801056Q006B012Q000400052Q0070000100013Q0020102Q01000100100006930001004800013Q00049F012Q004800012Q000100016Q0070000200013Q00201001020002001000061A010200480001000100049F012Q0048000100201100013Q000700129C010300086Q000400013Q00202Q0004000400104Q0001000400026Q00014Q0070000100013Q0020102Q01000100010020102Q0100010002000640012Q00500001000100049F012Q005000012Q0070000100013Q0020102Q0100010001001056000100024Q00652Q016Q00952Q016Q0070000100024Q005E2Q01000100012Q0024012Q00017Q00043Q0003053Q0056616C75652Q033Q00426F7803043Q0054657874030C3Q0046696E69736865644F6E6C79000E4Q00708Q005E012Q000100012Q00703Q00014Q0070000100013Q0020102Q01000100020020102Q01000100030010563Q000100012Q00703Q00013Q002010014Q00040006FC3Q000D0001000100049F012Q000D00012Q00703Q00024Q005E012Q000100012Q0024012Q00017Q00053Q00030D3Q0053657453752Q7072652Q73656403053Q0054772Q656E03063Q005374726F6B65030C3Q005472616E73706172656E6379029Q000C4Q00377Q00206Q00014Q000100018Q000200016Q00013Q00206Q00024Q000100023Q00202Q0001000100034Q00023Q000100302Q0002000400052Q004D012Q000200012Q0024012Q00017Q000B3Q00030D3Q0053657453752Q7072652Q73656403053Q0054772Q656E03063Q005374726F6B65030C3Q005472616E73706172656E6379026Q00F03F03053Q0056616C75652Q033Q00426F7803043Q0054657874030C3Q0046696E69736865644F6E6C7903073Q004F6E456E74657203053Q007063612Q6C01234Q003700015Q00202Q0001000100014Q00028Q0001000200014Q000100013Q00202Q0001000100024Q000200023Q00202Q0002000200034Q00033Q000100302Q0003000400052Q004D2Q01000300012Q0070000100024Q0070000200023Q0020100102000200070020100102000200080010560001000600022Q0070000100023Q0020102Q01000100090006930001001600013Q00049F012Q001600012Q0070000100034Q005E2Q01000100010006933Q002200013Q00049F012Q002200012Q0070000100043Q0020102Q010001000A0006930001002200013Q00049F012Q002200010012202Q01000B4Q0070000200043Q00201001020002000A2Q0070000300023Q0020100103000300062Q004D2Q01000300012Q0024012Q00017Q00033Q002Q033Q00426F7803043Q0054657874035Q00044Q00707Q002010014Q00010030053Q000200032Q0024012Q00017Q00053Q0003083Q00746F737472696E67034Q002Q033Q00426F7803043Q005465787403053Q0056616C756503133Q001220010300013Q00060B010400040001000100049F012Q00040001001291000400024Q00890003000200022Q00332Q0100033Q00202Q00033Q000300102Q00030004000100202Q00033Q000300202Q00030003000400104Q000500034Q00038Q00030001000100062Q000200110001000100049F012Q001100012Q0070000300014Q005E0103000100012Q00AA012Q00024Q0024012Q00017Q00013Q0003053Q0056616C756501033Q0020102Q013Q00012Q00AA2Q0100024Q0024012Q00017Q00023Q0003083Q00746F6E756D62657203053Q0056616C756501053Q0012CE000100013Q00202Q00023Q00024Q000100026Q00019Q0000017Q00053Q0003043Q004D61696403043Q004769766503073Q004368616E67656403073Q00436F2Q6E65637403053Q0056616C7565020D4Q008E01025Q00202Q00020002000100202Q00020002000200202Q00043Q000300202Q0004000400044Q000600016Q000400066Q00023Q00014Q000200013Q00202Q00033Q00052Q00040102000200012Q00AA012Q00024Q0024012Q00017Q00033Q00030B3Q0053657444697361626C65642Q033Q00426F78030C3Q00546578744564697461626C6502094Q007000025Q0020110002000200012Q0018010400014Q004D01020004000100201001023Q00022Q005F000300013Q0010560002000300032Q00AA012Q00024Q0024012Q00017Q00063Q0003043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C030A3Q00556E726567697374657203043Q00466C6167010C4Q00BA00015Q00202Q00010001000100202Q0001000100024Q00010002000100202Q00013Q000300202Q0001000100044Q0001000200014Q000100013Q00202Q00010001000500202Q00023Q00062Q00042Q01000200012Q0024012Q00017Q00083Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F5369676E616C03043Q0067616D65030A3Q0047657453657276696365030B3Q00546578745365727669636503073Q002Q5F696E6465782Q033Q006E657701184Q009900015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q00030002000200122Q000400043Q002011000400040005001291000600064Q008C0104000600022Q002A01055Q0010560005000700050006D400063Q000100052Q0018012Q00054Q0018012Q00034Q0018012Q00024Q0018012Q00014Q0018012Q00043Q0010560005000800062Q00AA010500024Q0024012Q00013Q00013Q00313Q00030C3Q007365746D6574617461626C6503043Q005479706503053Q004C6162656C03073Q004368616E6765642Q033Q006E657703083Q0047726F7570626F7803043Q0057726170010003063Q00412Q64526F7703063Q00486569676874026Q0030402Q033Q0047657403083Q0073697A652E726F772Q033Q00526F7703073Q00456C656D656E7403083Q00496E7374616E636503043Q005465787403043Q004E616D6503043Q0053697A6503053Q005544696D32026Q00F03F028Q00034Q0003083Q005269636854657874030B3Q00546578745772612Q706564030E3Q005465787459416C69676E6D656E7403043Q00456E756D2Q033Q00546F7003063Q0043656E746572030A3Q0054657874436F6C6F723303053Q00546F6B656E03053Q004D7574656403083Q00636F6C6F722E686903093Q00636F6C6F722E6D696403063Q00506172656E7403043Q00522Q6F742Q033Q0048697403063Q0041637469766503073Q0056697369626C6503043Q004D61696403043Q004769766503183Q0047657450726F70657274794368616E6765645369676E616C030C3Q004162736F6C75746553697A6503073Q00436F2Q6E65637403073Q00536574546578742Q033Q0053657403083Q0053657456616C756503083Q0047657456616C756503073Q0044657374726F79027C3Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q001220010200014Q002A01036Q007000046Q008C0102000400020030050002000200032Q0070000300013Q0020100103000300052Q00F2000300010002001056000200040003001056000200063Q002010010300010007002647000300120001000800049F012Q001200012Q001200036Q0065010300013Q00201100043Q00092Q002A01063Q00010006930003001A00013Q00049F012Q001A00010012910007000B3Q0006FC0007001E0001000100049F012Q001E00012Q0070000700023Q00201001070007000C0012910008000D4Q00890007000200020010560006000A00072Q005001040006000200102Q0002000E000400102Q0004000F00024Q000500033Q00202Q0005000500114Q00063Q000800302Q00060012000300122Q000700143Q00202Q00070007000500122Q000800153Q001291000900163Q001291000A00153Q001291000B00164Q008C0107000B00020010560006001300070020100107000100110006FC000700320001000100049F012Q00320001001291000700173Q001056000600110007002010010700010018002647000700370001000800049F012Q003700012Q001200076Q0065010700013Q0010560006001800070010560006001900030006930003004100013Q00049F012Q004100010012200107001B3Q00201001070007001A00201001070007001C0006FC000700440001000100049F012Q004400010012200107001B3Q00201001070007001A00201001070007001D0010560006001A00072Q0070000700033Q00201001070007001F0020100108000100200026470008004D0001000800049F012Q004D0001001291000800213Q0006FC0008004E0001000100049F012Q004E0001001291000800224Q00890007000200020010560006001E00070020100107000400240010560006002300072Q00890005000200020010560002001000050020100105000400250030050005002600080020100105000400250030050005002700080006D400053Q000100052Q0018012Q00034Q0018012Q00044Q00703Q00044Q0018012Q00024Q0018016Q00205800060004002800202Q00060006002900202Q00080004002400202Q00080008002A00122Q000A002B6Q0008000A000200202Q00080008002C4Q000A00056Q0008000A6Q00063Q00010006D400060001000100022Q0018012Q00044Q0018012Q00053Q0010230102002D000600202Q00060002002D00102Q0002002E000600202Q00060002002D00102Q0002002F0006000290010600023Q0010560002003000060006D400060003000100012Q0018012Q00043Q00105600020031000600201001060002001000201001060006001100100B0004001100064Q000600056Q0006000100014Q000200028Q00013Q00043Q00153Q0003043Q00522Q6F74030C3Q004162736F6C75746553697A6503013Q0058028Q00026Q006E4003053Q007063612Q6C03013Q0059026Q002C4003043Q006D6174682Q033Q006D6178026Q00F03F03043Q006365696C03083Q00496E7374616E636503083Q005465787453697A6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q003040026Q001040027Q004003073Q0052656672657368003F4Q00707Q0006FC3Q00040001000100049F012Q000400012Q0024012Q00014Q00703Q00013Q002010014Q0001002010014Q0002002010014Q00030026EC3Q000B0001000400049F012Q000B00010012913Q00053Q0012202Q0100063Q0006D400023Q000100032Q00703Q00024Q00703Q00034Q0018017Q005E0001000200020006930001001800013Q00049F012Q001800010006930002001800013Q00049F012Q001800010020100103000200070006FC000300190001000100049F012Q00190001001291000300083Q001220010400093Q0020E800040004000A00122Q0005000B3Q00122Q000600093Q00202Q00060006000C00122Q000700093Q00202Q00070007000A00122Q0008000B6Q000900033Q00202Q00090009000D00202Q00090009000E2Q008C0107000900022Q00CC0007000300072Q00F6000600074Q007301043Q00022Q0070000500013Q002010010500050001001220010600103Q0020100106000600110012910007000B3Q001291000800043Q001291000900043Q001220010A00093Q002010010A000A000A001291000B00124Q0070000C00033Q002010010C000C000D002010010C000C000E002060000C000C00132Q0036010C0004000C002060000C000C00142Q0072010A000C4Q007301063Q00020010560005000F00062Q0070000500043Q0020110005000500152Q00040105000200012Q0024012Q00013Q00013Q000B3Q00030B3Q004765745465787453697A6503083Q00496E7374616E6365030B3Q00436F6E74656E745465787403043Q005465787403083Q005465787453697A6503043Q00456E756D03043Q00466F6E74030A3Q00536F7572636553616E7303073Q00566563746F72322Q033Q006E6577025Q00408F4000184Q00707Q0020115Q00012Q0070000200013Q0020100102000200020020100102000200030006FC0002000A0001000100049F012Q000A00012Q0070000200013Q0020100102000200020020100102000200042Q0070000300013Q0020A701030003000200202Q00030003000500122Q000400063Q00202Q00040004000700202Q00040004000800122Q000500093Q00202Q00050005000A4Q000600023Q00122Q0007000B6Q000500079Q009Q008Q00017Q00063Q0003083Q00496E7374616E636503043Q005465787403083Q00746F737472696E67034Q0003073Q004368616E67656403043Q004669726502143Q00201001023Q0001001220010300033Q00060B010400050001000100049F012Q00050001001291000400044Q00890003000200020010560002000200032Q007000025Q00201001033Q00010020100103000300020010560002000200032Q0070000200014Q005E01020001000100201001023Q000500201100020002000600201001043Q00010020100104000400022Q004D0102000400012Q00AA012Q00024Q0024012Q00017Q00023Q0003083Q00496E7374616E636503043Q005465787401043Q0020102Q013Q00010020102Q01000100022Q00AA2Q0100024Q0024012Q00017Q00043Q0003043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C01084Q005F2Q015Q00202Q00010001000100202Q0001000100024Q00010002000100202Q00013Q000300202Q0001000100044Q0001000200016Q00017Q00033Q00030C3Q00636F72652F43726561746F72030B3Q00636F72652F5369676E616C2Q033Q006E6577010D4Q00182Q015Q001291000200014Q00890001000200022Q001801025Q001291000300024Q00890002000200022Q002A01035Q0006D400043Q000100022Q0018012Q00014Q0018012Q00023Q0010560003000300042Q00AA010300024Q0024012Q00013Q00013Q00263Q0003063Q00412Q64526F7703063Q00486569676874026Q00264003043Q0054657874034Q002Q033Q004E657703053Q004672616D6503043Q004E616D6503073Q0044697669646572030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F03083Q00506F736974696F6E03053Q005544696D3203093Q0066726F6D5363616C6503043Q0053697A65026Q00F03F026Q003240028Q0003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E776869746503163Q004261636B67726F756E645472616E73706172656E6379030E3Q00616C7068612E6C696E65536F667403063Q00506172656E7403043Q00522Q6F742Q033Q0048697403063Q00416374697665010003073Q0056697369626C6503083Q00436865636B626F7803043Q00547970652Q033Q00526F7703083Q00496E7374616E636503073Q004368616E67656403073Q0044657374726F7903073Q00456C656D656E74013F3Q00201100013Q00012Q002A01033Q00010030050003000200032Q008C2Q01000300020030050001000400052Q006B00025Q00202Q00020002000600122Q000300076Q00043Q000700302Q00040008000900122Q0005000B3Q00202Q00050005000C00122Q0006000D3Q00122Q0007000D6Q0005000700020010560004000A00050012200105000F3Q0020100105000500100012910006000D3Q0012E50007000D6Q00050007000200102Q0004000E000500122Q0005000F3Q00202Q00050005000C00122Q000600123Q00122Q000700133Q00122Q000800143Q00122Q000900126Q0005000900020010560004001100052Q007000055Q002010010500050016001291000600174Q00890005000200020010560004001500052Q007000055Q002010010500050016001291000600194Q008900050002000200105600040018000500201001050001001B0010560004001A00052Q008C01020004000200201001030001001C0030050003001D001E00201001030001001C0030050003001F001E0020100103000100200030050003001F001E2Q002A01033Q00040030050003002100090010560003002200010010560003002300022Q0070000400013Q00201001040004000C2Q00F20004000100020010560003002400040006D400043Q000100012Q0018012Q00013Q0010560003002500040010560001002600032Q00AA010300024Q0024012Q00013Q00013Q00043Q0003043Q004D616964030A3Q00446F436C65616E696E6703073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C01084Q005F2Q015Q00202Q00010001000100202Q0001000100024Q00010002000100202Q00013Q000300202Q0001000100044Q0001000200016Q00017Q00173Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E03093Q00636F72652F4D61696403043Q0067616D65030A3Q0047657453657276696365030B3Q005465787453657276696365025Q00406F40026Q001840026Q0030402Q033Q006E657703043Q00496E666F030C3Q00636F6C6F722E612Q63656E7403073Q0053752Q63652Q7303043Q005761726E030A3Q00636F6C6F722E7761726E03053Q00452Q726F72030C3Q00636F6C6F722E64616E67657203043Q00496E697403063Q004E6F7469667903053Q00436F756E7403053Q00436C65617203073Q0044657374726F7901464Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q0089000400020002001220010500053Q002011000500050006001291000700074Q008C0105000700022Q002A01065Q001291000700083Q001291000800093Q0012910009000A4Q001E000A000A4Q002A010B5Q002010010C0004000B2Q00F2000C000100022Q002A010D3Q0004003005000D000C000D003005000D000E000D003005000D000F0010003005000D001100120006D4000E3Q000100062Q0018012Q000A4Q0018012Q00014Q0018012Q00094Q0018012Q00074Q0018012Q000C4Q0018012Q000B3Q00105600060013000E0006D4000E0001000100032Q0018012Q000B4Q0018012Q00034Q0018012Q00083Q0006D4000F0002000100022Q0018012Q000B4Q0018012Q000E3Q0006D4001000030001000B2Q0018012Q000A4Q0018012Q00054Q0018012Q00024Q0018012Q00074Q0018012Q00044Q0018012Q00014Q0018012Q000D4Q0018012Q000B4Q0018012Q000E4Q0018012Q00034Q0018012Q000F3Q0010560006001400100006D400100004000100012Q0018012Q000B3Q0010560006001500100006D400100005000100012Q0018012Q000B3Q0010560006001600100006D400100006000100032Q0018012Q00064Q0018012Q000C4Q0018012Q000A3Q0010560006001700102Q00AA010600024Q0024012Q00013Q00073Q00123Q0003073Q0044657374726F792Q033Q004E657703053Q004672616D6503043Q004E616D65030D3Q004E6F74696669636174696F6E73030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00F03F03083Q00506F736974696F6E03053Q005544696D3203043Q0053697A65030A3Q0066726F6D4F2Q6673657403163Q004261636B67726F756E645472616E73706172656E637903063Q005A496E646578025Q00C0824003063Q00506172656E7403043Q0047697665012F4Q007000015Q0006930001000600013Q00049F012Q000600012Q007000015Q0020110001000100012Q00042Q01000200012Q0070000100013Q0020ED00010001000200122Q000200036Q00033Q000700302Q00030004000500122Q000400073Q00202Q00040004000800122Q000500093Q00122Q000600096Q00040006000200102Q0003000600040012200104000B3Q00200700040004000800122Q000500096Q000600026Q000600063Q00122Q000700096Q000800026Q000800086Q00040008000200102Q0003000A000400122Q0004000B3Q00201001040004000D2Q0070000500033Q001291000600094Q008C0104000600020010560003000C00040030050003000E00090030050003000F0010001056000300114Q008C2Q01000300022Q00952Q016Q0070000100043Q0020110001000100122Q007000036Q004D2Q01000300012Q002A2Q016Q00952Q0100054Q007000016Q00AA2Q0100024Q0024012Q00017Q00093Q00028Q00026Q00F03F026Q00F0BF03053Q0054772Q656E03053Q004672616D6503083Q00506F736974696F6E03053Q005544696D322Q033Q006E657703063Q00486569676874001B3Q0012913Q00014Q007000016Q0001000100013Q001291000200023Q001291000300033Q0004F30001001A00012Q007000056Q00440005000500044Q000600013Q00202Q00060006000400202Q0007000500054Q00083Q000100122Q000900073Q00202Q00090009000800122Q000A00013Q00122Q000B00013Q00122Q000C00026Q000D8Q0009000D000200102Q0008000600094Q00060008000100202Q0006000500094Q00063Q00064Q000700028Q000600070004510001000600012Q0024012Q00017Q00053Q0003063Q0069706169727303053Q007461626C6503063Q0072656D6F766503043Q004D616964030A3Q00446F436C65616E696E6701143Q0012202Q0100014Q007000026Q005E00010002000300049F012Q000C000100066A0105000C00013Q00049F012Q000C0001001220010600023Q0020660106000600034Q00078Q000800046Q00060008000100044Q000E0001000677000100040001000200049F012Q000400010020102Q013Q00040020110001000100052Q00042Q01000200012Q0070000100014Q005E2Q01000100012Q0024012Q00017Q004E3Q0003073Q0056617269616E7403043Q00496E666F03053Q005469746C6503063Q006175726F726103043Q0054657874034Q0003083Q004475726174696F6E026Q001040028Q0003053Q007063612Q6C03013Q0059026Q002C4003043Q006D6174682Q033Q006D61782Q033Q006D696E025Q00805640027Q0040026Q003740026Q00244003043Q004D6169642Q033Q006E657703063Q004865696768742Q033Q004E657703053Q004672616D6503043Q004E616D6503053Q00546F617374030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00F03F03083Q00506F736974696F6E03053Q005544696D32026Q00444003043Q0053697A65030A3Q0066726F6D4F2Q6673657403103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030E3Q00636F6C6F722E656C65766174656403163Q004261636B67726F756E645472616E73706172656E6379030B3Q00616C7068612E706F70757003103Q00436C69707344657363656E64616E74732Q0103063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E626F7803063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503043Q0047697665026Q002240026Q002040026Q0032C0026Q002A40030A3Q0054657874436F6C6F7233030C3Q00636F6C6F722E612Q63656E7403043Q00426F647903093Q00636F6C6F722E6D6964030B3Q00546578745772612Q706564030E3Q005465787459416C69676E6D656E7403043Q00456E756D2Q033Q00546F7003083Q0050726F6772652Q73030A3Q005465787442752Q746F6E03093Q0066726F6D5363616C6503043Q0067616D65030A3Q0047657453657276696365030C3Q0054772Q656E5365727669636503063Q0043726561746503093Q0054772Q656E496E666F030B3Q00456173696E675374796C6503063Q004C696E65617203043Q00506C617903073Q004469736D692Q7303113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E65637403043Q007461736B03053Q0064656C617903063Q0048616E646C650132013Q007000015Q0006FC000100050001000100049F012Q000500012Q001E000100014Q00AA2Q0100023Q0006FC3Q00090001000100049F012Q000900012Q002A2Q016Q0018012Q00013Q0020102Q013Q00010006FC0001000D0001000100049F012Q000D0001001291000100023Q00201001023Q00030006FC000200110001000100049F012Q00110001001291000200043Q00201001033Q00050006FC000300150001000100049F012Q00150001001291000300063Q00201001043Q00070006FC000400190001000100049F012Q00190001001291000400083Q001291000500093Q002696000300350001000600049F012Q003500010012200106000A3Q0006D400073Q000100042Q00703Q00014Q0018012Q00034Q00703Q00024Q00703Q00034Q005E0006000200070006930006002A00013Q00049F012Q002A00010006930007002A00013Q00049F012Q002A000100201001080007000B00060B0105002B0001000800049F012Q002B00010012910005000C3Q0012200108000D3Q00201001080008000E0012910009000C3Q001220010A000D3Q002010010A000A000F2Q0018010B00053Q001291000C00104Q0072010A000C4Q007301083Q00022Q0018010500083Q0026960003003A0001000600049F012Q003A000100103D0006001100050006FC0006003B0001000100049F012Q003B0001001291000600093Q00103D0006001200060020600006000600132Q002A01073Q00022Q0070000800043Q0020100108000800152Q00F20008000100020010560007001400080010560007001600062Q006B000800053Q00202Q00080008001700122Q000900186Q000A3Q000800302Q000A0019001A00122Q000B001C3Q00202Q000B000B001500122Q000C00093Q00122Q000D001D6Q000B000D0002001056000A001B000B001220010B001F3Q002010010B000B0015001291000C00094Q0070000D00033Q002094000D000D002000122Q000E001D3Q00122Q000F00096Q000B000F000200102Q000A001E000B00122Q000B001F3Q00202Q000B000B00224Q000C00036Q000D00066Q000B000D0002001056000A0021000B2Q0070000B00053Q00203C000B000B002400122Q000C00256Q000B0002000200102Q000A0023000B4Q000B00053Q00202Q000B000B002400122Q000C00276Q000B0002000200102Q000A0026000B00302Q000A002800292Q0070000B5Q001056000A002A000B2Q008C0108000A00022Q0070000900053Q00201001090009002B2Q0070000A00023Q002010010A000A002C001291000B002D4Q0089000A000200022Q0018010B00084Q004D0109000B00012Q0093010900053Q00202Q00090009002E4Q000A00083Q00122Q000B002F3Q00122Q000C00306Q0009000C000100102Q00070018000800202Q00090007001400202Q0009000900314Q000B00084Q004D0109000B00012Q0070000900053Q0020100109000900052Q002A010A3Q00060030B3000A0019000300122Q000B001F3Q00202Q000B000B002200122Q000C00323Q00122Q000D00336Q000B000D000200102Q000A001E000B00122Q000B001F3Q00202Q000B000B001500122Q000C001D3Q001291000D00343Q001291000E00093Q001291000F00354Q008C010B000F0002001056000A0021000B001056000A000500022Q0070000B00053Q002010010B000B00242Q0070000C00064Q0016010C000C00010006FC000C00980001000100049F012Q00980001001291000C00374Q0089000B00020002001056000A0036000B001056000A002A00082Q0004010900020001002696000300BD0001000600049F012Q00BD00012Q0070000900053Q0020100109000900052Q002A010A3Q00080030B3000A0019003800122Q000B001F3Q00202Q000B000B002200122Q000C00323Q00122Q000D00126Q000B000D000200102Q000A001E000B00122Q000B001F3Q00202Q000B000B001500122Q000C001D3Q001291000D00343Q001291000E00094Q0018010F00054Q008C010B000F0002001056000A0021000B001056000A000500032Q0070000B00053Q002010010B000B0024001291000C00394Q0089000B00020002001056000A0036000B003005000A003A0029001220010B003C3Q002010010B000B003B002010010B000B003D001056000A003B000B001056000A002A00082Q00040109000200012Q0070000900053Q0020ED00090009001700122Q000A00186Q000B3Q000700302Q000B0019003E00122Q000C001C3Q00202Q000C000C001500122Q000D00093Q00122Q000E001D6Q000C000E000200102Q000B001B000C001220010C001F3Q002010010C000C0015001291000D00093Q001242010E00093Q00122Q000F001D3Q00122Q001000096Q000C0010000200102Q000B001E000C00122Q000C001F3Q00202Q000C000C001500122Q000D001D3Q00122Q000E00093Q00122Q000F00093Q0012910010001D4Q008C010C00100002001056000B0021000C2Q0070000C00053Q002010010C000C00242Q0070000D00064Q0016010D000D00010006FC000D00DF0001000100049F012Q00DF0001001291000D00374Q0089000C00020002001056000B0023000C003005000B00260009001056000B002A00082Q008C0109000B00022Q0070000A00053Q002010010A000A0017001291000B003F4Q002A010C3Q0004001220010D001F3Q002010010D000D0040001291000E001D3Q0012C1000F001D6Q000D000F000200102Q000C0021000D00302Q000C0026001D00302Q000C0005000600102Q000C002A00084Q000A000C00024Q000B00076Q000C00076Q000C000C3Q002060000C000C001D2Q0078000B000C00074Q000B00086Q000B0001000100122Q000B00413Q00202Q000B000B004200122Q000D00436Q000B000D000200202Q000B000B00444Q000D00093Q00122Q000E00453Q002010010E000E00152Q0031010F00043Q00122Q0010003C3Q00202Q00100010004600202Q0010001000474Q000E001000024Q000F3Q000100122Q0010001F3Q00202Q00100010001500122Q001100093Q00122Q001200093Q001291001300093Q0012910014001D4Q008C011000140002001056000F002100102Q008C010B000F0002002011000C000B00482Q0004010C00020001002010010C00070014002011000C000C00310006D4000E0001000100012Q0018012Q000B4Q004D010C000E00012Q002A010C6Q0065010D5Q0006D4000E0002000100062Q0018012Q000D4Q00703Q00094Q0018012Q00084Q00703Q00034Q00703Q000A4Q0018012Q00073Q00109F000C0049000E00202Q000E0007001400202Q000E000E003100202Q0010000A004A00202Q00100010004B0006D400120003000100012Q0018012Q000C4Q0072011000124Q0061010E3Q0001001220010E004C3Q002010010E000E004D2Q0018010F00043Q0006D400100004000100012Q0018012Q000C4Q004D010E001000010010560007004E000C2Q00AA010C00024Q0024012Q00013Q00053Q000A3Q00030B3Q004765745465787453697A652Q033Q0047657403073Q00746578742E756903043Q00456E756D03043Q00466F6E74030A3Q00536F7572636553616E7303073Q00566563746F72322Q033Q006E6577026Q003240026Q00794000134Q00707Q0020115Q00012Q0070000200014Q0070000300023Q002010010300030002001291000400034Q0089000300020002001220010400043Q002010010400040005002010010400040006001220010500073Q0020100105000500082Q0070000600033Q00203E0006000600090012910007000A4Q0072010500074Q0092017Q00358Q0024012Q00017Q00013Q0003053Q007063612Q6C00053Q001220012Q00013Q0006D400013Q000100012Q00708Q0004012Q000200012Q0024012Q00013Q00013Q00013Q0003063Q0043616E63656C00044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q000C3Q0003053Q0054772Q656E03083Q00506F736974696F6E03053Q005544696D322Q033Q006E6577028Q00026Q004440026Q00F03F03013Q005903063Q004F2Q6673657403043Q007461736B03053Q0064656C617903083Q004475726174696F6E01204Q007000015Q0006930001000400013Q00049F012Q000400012Q0024012Q00014Q00652Q0100014Q00492Q018Q000100013Q00202Q0001000100014Q000200026Q00033Q000100122Q000400033Q00202Q00040004000400122Q000500056Q000600033Q00202Q00060006000600122Q000700076Q000800023Q00202Q00080008000200202Q00080008000800202Q0008000800094Q00040008000200102Q0003000200044Q00010003000100122Q0001000A3Q00202Q00010001000B4Q000200013Q00202Q00020002000C0006D400033Q000100022Q00703Q00044Q00703Q00054Q004D2Q01000300012Q0024012Q00013Q00018Q00044Q00708Q0070000100014Q0004012Q000200012Q0024012Q00017Q00013Q0003073Q004469736D692Q7300044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00013Q0003073Q004469736D692Q7300044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00019Q003Q00044Q00708Q00018Q00AA012Q00024Q0024012Q00017Q00053Q00026Q00F03F026Q00F0BF03043Q004D616964030A3Q00446F436C65616E696E672Q000E4Q00708Q00017Q001291000100013Q001291000200023Q0004F33Q000D00012Q007000046Q008601040004000300202Q00040004000300202Q0004000400044Q0004000200014Q00045Q00202Q0004000300050004513Q000500012Q0024012Q00017Q00023Q0003053Q00436C656172030A3Q00446F436C65616E696E6700094Q00FD7Q00206Q00016Q000100016Q00013Q00206Q00026Q000200019Q006Q00028Q00017Q000D3Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E03093Q00636F72652F4D61696403043Q0067616D65030A3Q0047657453657276696365030B3Q005465787453657276696365025Q0080714003043Q00496E697403053Q00436C6F736503063Q0049734F70656E03043Q0053686F7703073Q0044657374726F79012D4Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q0089000400020002001220010500053Q002011000500050006001291000700074Q008C0105000700022Q002A01065Q001291000700084Q001E000800093Q0006D4000A3Q000100012Q0018012Q00083Q00105600060009000A0006D4000A0001000100012Q0018012Q00093Q0010560006000A000A0006D4000A0002000100012Q0018012Q00093Q0010560006000B000A0006D4000A0003000100092Q0018012Q00084Q0018012Q00064Q0018012Q00044Q0018012Q00054Q0018012Q00024Q0018012Q00074Q0018012Q00014Q0018012Q00034Q0018012Q00093Q0010560006000C000A0006D4000A0004000100022Q0018012Q00064Q0018012Q00083Q0010560006000D000A2Q00AA010600024Q0024012Q00013Q00057Q0001044Q0095017Q007000016Q00AA2Q0100024Q0024012Q00017Q00023Q0003043Q004D616964030A3Q00446F436C65616E696E67000B4Q00707Q0006FC3Q00040001000100049F012Q000400012Q0024012Q00014Q00708Q001E000100014Q00952Q015Q0020102Q013Q00010020110001000100022Q00042Q01000200012Q0024012Q00017Q00015Q00074Q00707Q0026473Q00040001000100049F012Q000400012Q00128Q0065012Q00014Q00AA012Q00024Q0024012Q00017Q00643Q0003053Q00436C6F73652Q033Q006E657703073Q0042752Q746F6E7303043Q005465787403023Q006F6B034Q00028Q0003053Q007063612Q6C03043Q006D6174682Q033Q006D6178026Q0030402Q033Q006D696E03013Q0059026Q006440025Q00802Q40026Q002840026Q003440026Q002A402Q033Q004E6577030A3Q005465787442752Q746F6E03043Q004E616D6503053Q00536372696D03043Q0053697A6503053Q005544696D3203093Q0066726F6D5363616C65026Q00F03F03103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030B3Q00636F6C6F722E626C61636B03163Q004261636B67726F756E645472616E73706172656E6379030F3Q004175746F42752Q746F6E436F6C6F72010003063Q005A496E646578025Q00E0854003063Q00506172656E7403043Q004769766503053Q0054772Q656E2Q033Q00476574030B3Q00616C7068612E736372696D03053Q004672616D6503063Q004469616C6F67030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F03083Q00506F736974696F6E030A3Q0066726F6D4F2Q66736574030E3Q00636F6C6F722E656C657661746564030B3Q00616C7068612E706F707570025Q00E8854003063Q00436F726E6572030A3Q007261646975732E626F7803063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503053Q005469746C65026Q003AC0026Q002E40030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903083Q005465787453697A6503043Q00426F647903093Q00636F6C6F722E6D6964030B3Q00546578745772612Q7065642Q01030E3Q005465787459416C69676E6D656E7403043Q00456E756D2Q033Q00546F70026Q002AC0030C3Q0055494C6973744C61796F7574030D3Q0046692Q6C446972656374696F6E030A3Q00486F72697A6F6E74616C03073Q0050612Q64696E6703043Q005544696D026Q00104003093Q00536F72744F72646572030B3Q004C61796F75744F7264657203063Q0069706169727303073Q0056617269616E7403073Q005072696D61727903063Q0044616E67657203063Q0062752Q746F6E026Q0010C0030C3Q00636F6C6F722E612Q63656E74030A3Q00616C7068612E77652Q6C030A3Q007261646975732E63746C03083Q0055495374726F6B6503053Q00436F6C6F72030C3Q00636F6C6F722E64616E676572030C3Q005472616E73706172656E637903093Q00546869636B6E652Q73030F3Q00412Q706C795374726F6B654D6F646503063Q00426F72646572030E3Q00636F6C6F722E612Q63656E744F6E030E3Q005465787458416C69676E6D656E7403063Q0043656E74657203113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374030B3Q004469736D692Q7361626C6503043Q004D61696403053Q0050616E656C01A0013Q007000015Q0006FC000100050001000100049F012Q000500012Q001E000100014Q00AA2Q0100024Q0070000100013Q0020102Q01000100012Q005E2Q01000100010006FC3Q000C0001000100049F012Q000C00012Q002A2Q016Q0018012Q00014Q0070000100023Q0020102Q01000100022Q00F200010001000200201001023Q00030006FC000200160001000100049F012Q001600012Q002A010200014Q002A01033Q00010030050003000400052Q002500020001000100201001033Q00040006FC0003001A0001000100049F012Q001A0001001291000300063Q001291000400073Q002696000300350001000600049F012Q00350001001220010500083Q0006D400063Q000100042Q00703Q00034Q0018012Q00034Q00703Q00044Q00703Q00054Q005E000500020006001220010700093Q00201001070007000A0012910008000B3Q001220010900093Q00201001090009000C0006930005003000013Q00049F012Q003000010006930006003000013Q00049F012Q00300001002010010A0006000D0006FC000A00310001000100049F012Q00310001001291000A000B3Q001291000B000E4Q00720109000B4Q007301073Q00022Q0018010400073Q00103D0005000F00040020600005000500100020600005000500110020600005000500122Q006B000600063Q00202Q00060006001300122Q000700146Q00083Q000800302Q00080015001600122Q000900183Q00202Q00090009001900122Q000A001A3Q00122Q000B001A6Q0009000B00020010560008001700092Q0070000900063Q00201001090009001C001291000A001D4Q00890009000200020010560008001B00090030050008001E001A0030050008000400060030050008001F002000306E0008002100224Q00095Q00102Q0008002300094Q00060008000200202Q0007000100244Q000900066Q0007000900014Q000700073Q00202Q0007000700254Q000800064Q002A01093Q00012Q0070000A00043Q002010010A000A0026001291000B00274Q0089000A000200020010560009001E000A2Q004D0107000900012Q006B000700063Q00202Q00070007001300122Q000800286Q00093Q000800302Q00090015002900122Q000A002B3Q00202Q000A000A000200122Q000B002C3Q00122Q000C002C6Q000A000C00020010560009002A000A001220010A00183Q002010010A000A0019001291000B002C3Q001291000C002C4Q008C010A000C00020010560009002D000A001220010A00183Q002010010A000A002E2Q0070000B00054Q0018010C00054Q008C010A000C000200105600090017000A2Q0070000A00063Q00203C000A000A001C00122Q000B002F6Q000A0002000200102Q0009001B000A4Q000A00063Q00202Q000A000A001C00122Q000B00306Q000A0002000200102Q0009001E000A00302Q0009002100310010560009002300062Q008C0107000900022Q0070000800063Q0020100108000800322Q0070000900043Q002010010900090026001291000A00334Q008900090002000200206000090009001A2Q0018010A00074Q004D0108000A00012Q0070000800063Q0020100108000800342Q0018010900073Q001291000A00353Q0012EA000B00366Q0008000B00014Q000800063Q00202Q0008000800044Q00093Q000700302Q00090015003700122Q000A00183Q00202Q000A000A002E00122Q000B00123Q00122Q000C00124Q008C010A000C00020010560009002D000A001220010A00183Q002010010A000A0002001291000B001A3Q001291000C00383Q001291000D00073Q001291000E00394Q008C010A000E000200105600090017000A002010010A3Q00370006FC000A00A60001000100049F012Q00A60001001291000A00063Q00105600090004000A2Q0070000A00063Q002010010A000A001C001291000B003B4Q0089000A000200020010560009003A000A0030050009003C00100010560009002300072Q0004010800020001002696000300D00001000600049F012Q00D000012Q0070000800063Q0020100108000800042Q002A01093Q00080030B300090015003D00122Q000A00183Q00202Q000A000A002E00122Q000B00123Q00122Q000C000F6Q000A000C000200102Q0009002D000A00122Q000A00183Q00202Q000A000A000200122Q000B001A3Q001291000C00383Q001291000D00074Q0018010E00044Q008C010A000E000200105600090017000A0010560009000400032Q0070000A00063Q002010010A000A001C001291000B003E4Q0089000A000200020010560009003A000A0030050009003F0040001220010A00423Q002010010A000A0041002010010A000A004300105600090041000A0010560009002300072Q00040108000200012Q0070000800063Q0020ED00080008001300122Q000900286Q000A3Q000600302Q000A0015000300122Q000B002B3Q00202Q000B000B000200122Q000C00073Q00122Q000D001A6Q000B000D000200102Q000A002A000B001220010B00183Q002010010B000B0002001291000C00073Q001242010D00123Q00122Q000E001A3Q00122Q000F00446Q000B000F000200102Q000A002D000B00122Q000B00183Q00202Q000B000B000200122Q000C001A3Q00122Q000D00383Q00122Q000E00073Q001291000F00114Q008C010B000F0002001056000A0017000B003005000A001E001A001056000A002300072Q008C0108000A00022Q0070000900063Q002010010900090013001291000A00454Q002A010B3Q0004001220010C00423Q002010010C000C0046002010010C000C0047001056000B0046000C001220010C00493Q002010010C000C0002001291000D00073Q001291000E004A4Q008C010C000E0002001056000B0048000C001220010C00423Q002010010C000C004B002010010C000C004C001056000B004B000C001056000B002300082Q004D0109000B00010012200109004D4Q0018010A00024Q005E00090002000B00049F012Q008C2Q01002010010E000D004E002696000E000A2Q01004F00049F012Q000A2Q012Q0012000E6Q0065010E00013Q002010010F000D004E002696000F000F2Q01005000049F012Q000F2Q012Q0012000F6Q0065010F00014Q0070001000063Q002010011000100013001291001100144Q002A01123Q00070020100113000D00040006FC0013001A2Q01000100049F012Q001A2Q01001291001300514Q00180114000C4Q006B0113001300140010560012001500130012E6001300183Q00202Q0013001300024Q001400023Q00102Q0014001A00144Q001500023Q00202Q00150015001A00102Q0015005200154Q001600026Q00150015001600122Q0016001A3Q00122Q001700076Q00130017000200102Q0012001700134Q001300063Q00202Q00130013001C00062Q000E002F2Q013Q00049F012Q002F2Q01001291001400533Q0006FC001400302Q01000100049F012Q00302Q01001291001400354Q00890013000200020010560012001B0013000693000E00372Q013Q00049F012Q00372Q01001291001300073Q0006FC001300402Q01000100049F012Q00402Q01000693000F003C2Q013Q00049F012Q003C2Q010012910013001A3Q0006FC001300402Q01000100049F012Q00402Q012Q0070001300063Q00201001130013001C001291001400544Q00890013000200020010560012001E001300301201120004000600102Q0012004C000C00102Q0012002300084Q0010001200024Q001100063Q00202Q0011001100324Q001200043Q00202Q00120012002600122Q001300556Q0012000200024Q001300106Q00110013000100062Q000F00602Q013Q00049F012Q00602Q012Q0070001100063Q00202101110011001300122Q001200566Q00133Q00054Q001400043Q00202Q00140014002600122Q001500586Q00140002000200102Q00130057001400302Q00130059002C00302Q0013005A001A001220011400423Q00201001140014005B00201001140014005C0010560013005B00140010560013002300102Q004D0111001300012Q0070001100063Q0020100111001100042Q002A01123Q0005001220011300183Q0020100113001300190012910014001A3Q0012910015001A4Q008C0113001500020010560012001700130020100113000D00040006FC0013006D2Q01000100049F012Q006D2Q01001291001300053Q0010560012000400132Q0070001300063Q00201001130013001C000693000E00752Q013Q00049F012Q00752Q010012910014005D3Q0006FC0014007B2Q01000100049F012Q007B2Q01000693000F007A2Q013Q00049F012Q007A2Q01001291001400583Q0006FC0014007B2Q01000100049F012Q007B2Q010012910014003B4Q00890013000200020010560012003A0013001220011300423Q00201001130013005E00201001130013005F0010560012005E00130010560012002300102Q00040111000200010020110011000100240020100113001000600020110013001300610006D400150001000100022Q00703Q00014Q0018012Q000D4Q0072011300154Q006101113Q00012Q00A8010C5Q000677000900062Q01000200049F012Q00062Q0100201001093Q0062002696000900982Q01002000049F012Q00982Q01002011000900010024002010010B00060060002011000B000B00610006D4000D0002000100012Q00703Q00014Q0072010B000D4Q006101093Q00012Q002A01093Q00030010560009006300010010560009006400070010560009001600062Q0095010900084Q0070000900084Q00AA010900024Q0024012Q00013Q00033Q000A3Q00030B3Q004765745465787453697A652Q033Q0047657403073Q00746578742E756903043Q00456E756D03043Q00466F6E74030A3Q00536F7572636553616E7303073Q00566563746F72322Q033Q006E6577026Q003A40026Q00794000134Q00707Q0020115Q00012Q0070000200014Q0070000300023Q002010010300030002001291000400034Q0089000300020002001220010400043Q002010010400040005002010010400040006001220010500073Q0020100105000500082Q0070000600033Q00203E0006000600090012910007000A4Q0072010500074Q0092017Q00358Q0024012Q00017Q00063Q0003053Q00436C6F736503083Q0043612Q6C6261636B03053Q007063612Q6C03043Q007761726E03203Q005B4175726F72615D206469616C6F672063612Q6C6261636B20652Q726F723A2003083Q00746F737472696E6700154Q00707Q002010014Q00012Q005E012Q000100012Q00703Q00013Q002010014Q00020006933Q001400013Q00049F012Q00140001001220012Q00034Q0070000100013Q0020102Q01000100022Q005E3Q000200010006FC3Q00140001000100049F012Q00140001001220010200043Q001280000300053Q00122Q000400066Q000500016Q0004000200024Q0003000300044Q0002000200012Q0024012Q00017Q00013Q0003053Q00436C6F736500044Q00707Q002010014Q00012Q005E012Q000100012Q0024012Q00017Q00013Q0003053Q00436C6F736500064Q00707Q002010014Q00012Q005E012Q000100012Q001E8Q0095012Q00014Q0024012Q00017Q00123Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E03093Q00636F72652F5574696C03093Q00636F72652F4D61696403043Q0067616D65030A3Q004765745365727669636503103Q0055736572496E70757453657276696365030B3Q005465787453657276696365029A5Q99C93F026Q0069402Q033Q006E6577028Q0003043Q00496E697403043Q0053686F7703043Q004869646503063Q00412Q7461636803073Q0044657374726F79014B4Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q00890004000200022Q001801055Q001291000600054Q0089000500020002001220010600063Q002011000600060007001291000800084Q008C010600080002001220010700063Q002011000700070007001291000900094Q008C0107000900022Q002A01085Q0012910009000A3Q001291000A000B4Q001E000B000D3Q002010010E0005000C2Q00F2000E00010002001291000F000D4Q001E001000103Q0006D400113Q000100062Q0018012Q000E4Q0018012Q000B4Q0018012Q000C4Q0018012Q00014Q0018012Q00024Q0018012Q000D3Q0010560008000E00110006D400110001000100032Q0018012Q000C4Q0018012Q00064Q0018012Q00043Q0006D400120002000100092Q0018012Q000C4Q0018012Q000A4Q0018012Q00074Q0018012Q00024Q0018012Q000D4Q0018012Q00114Q0018012Q00034Q0018012Q00104Q0018012Q00063Q0010560008000F00120006D400120003000100052Q0018012Q000F4Q0018012Q00104Q0018012Q000C4Q0018012Q00034Q0018012Q000D3Q0010560008001000120006D400120004000100032Q0018012Q000F4Q0018012Q00094Q0018012Q00083Q0010560008001100120006D400120005000100052Q0018012Q00084Q0018012Q000E4Q0018012Q000B4Q0018012Q000C4Q0018012Q000D3Q0010560008001200122Q00AA010800024Q0024012Q00013Q00063Q002A3Q00030A3Q00446F436C65616E696E672Q033Q004E657703053Q004672616D6503043Q004E616D6503073Q00542Q6F6C74697003043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q00244003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E030E3Q00636F6C6F722E656C65766174656403163Q004261636B67726F756E645472616E73706172656E6379026Q00F03F03073Q0056697369626C65010003063Q005A496E646578026Q00894003063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503043Q004769766503043Q005465787403083Q00506F736974696F6E026Q001C40026Q0010402Q033Q006E6577026Q002CC0026Q0020C0034Q00030A3Q0054657874436F6C6F723303083Q00636F6C6F722E6869030B3Q00546578745772612Q7065642Q01030E3Q005465787459416C69676E6D656E7403043Q00456E756D2Q033Q00546F7003103Q00546578745472616E73706172656E637901524Q007000015Q0020110001000100012Q00042Q01000200012Q0095012Q00014Q006B000100033Q00202Q00010001000200122Q000200036Q00033Q000700302Q00030004000500122Q000400073Q00202Q00040004000800122Q000500093Q00122Q000600096Q0004000600020010560003000600042Q0070000400033Q00201001040004000B0012910005000C4Q00890004000200020010560003000A00040030050003000D000E0030050003000F001000305C0103001100124Q000400013Q00102Q0003001300044Q0001000300024Q000100026Q000100033Q00202Q0001000100144Q000200043Q00202Q00020002001500122Q000300164Q00890002000200022Q0070000300024Q004D2Q01000300012Q0070000100033Q0020102Q01000100172Q0070000200023Q001291000300183Q001291000400194Q004D2Q01000400012Q007000015Q00201100010001001A2Q0070000300024Q004D2Q01000300012Q0070000100033Q0020102Q010001001B2Q002A01023Q00090030B300020004001B00122Q000300073Q00202Q00030003000800122Q0004001D3Q00122Q0005001E6Q00030005000200102Q0002001C000300122Q000300073Q00202Q00030003001F00122Q0004000E3Q001291000500203Q0012910006000E3Q001291000700214Q008C0103000700020010560002000600030030050002001B00222Q0070000300033Q00201001030003000B001291000400244Q0089000300020002001056000200230003003005000200250026001220010300283Q0020100103000300270020100103000300290010560002002700030030050002002A000E2Q0070000300023Q0010560002001300032Q00890001000200022Q00952Q0100054Q0070000100024Q00AA2Q0100024Q0024012Q00017Q00153Q0003073Q0056697369626C6503103Q004765744D6F7573654C6F636174696F6E03093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503073Q00566563746F72322Q033Q006E6577026Q009E40025Q00E09040030C3Q004162736F6C75746553697A6503053Q00636C616D7003013Q0058026Q002840026Q00144003043Q006D6174682Q033Q006D617803013Q0059026Q00304003083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q66736574003D4Q00707Q0006933Q000700013Q00049F012Q000700012Q00707Q002010014Q00010006FC3Q00080001000100049F012Q000800012Q0024012Q00014Q00703Q00013Q0020115Q00022Q00893Q000200020012202Q0100033Q0020102Q01000100040006930001001200013Q00049F012Q001200010020100102000100050006FC000200170001000100049F012Q00170001001220010200063Q002010010200020007001291000300083Q001291000400094Q008C0102000400022Q007000035Q00201001030003000A2Q0070000400023Q00201001040004000B00201001053Q000C00206000050005000D0012910006000E3Q0012200107000F3Q0020100107000700100012910008000E3Q00201001090002000C002010010A0003000C2Q002Q01090009000A00203E00090009000E2Q0072010700094Q007301043Q00022Q0070000500023Q00201001050005000B00201001063Q00110020600006000600120012910007000E3Q0012200108000F3Q0020100108000800100012910009000E3Q002010010A00020011002010010B000300112Q002Q010A000A000B00203E000A000A000E2Q00720108000A4Q007301053Q00022Q007000065Q001220010700143Q0020100107000700152Q0018010800044Q0018010900054Q008C0107000900020010560006001300072Q0024012Q00017Q001A4Q00034Q00026Q00304003053Q007063612Q6C03043Q006D6174682Q033Q006D696E03013Q0058026Q002C40027Q004003013Q0059026Q00204003043Q005465787403043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403073Q0056697369626C652Q0103053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E63792Q033Q00476574030B3Q00616C7068612E706F70757003103Q00546578745472616E73706172656E6379028Q00030A3Q00446973636F2Q6E656374030C3Q00496E7075744368616E67656403073Q00436F2Q6E656374014A4Q007000015Q0006930001000700013Q00049F012Q000700010026963Q00070001000100049F012Q000700010026473Q00080001000200049F012Q000800012Q0024012Q00014Q0070000100013Q001291000200033Q001220010300043Q0006D400043Q000100042Q00703Q00024Q0018017Q00703Q00034Q00703Q00014Q005E0003000200040006930003001F00013Q00049F012Q001F00010006930004001F00013Q00049F012Q001F0001001220010500053Q0020B70005000500064Q000600013Q00202Q00070004000700202Q00070007000800202Q0007000700094Q0005000700024Q000100053Q00202Q00050004000A00202Q00020005000B2Q0070000500043Q0010560005000C4Q007000055Q0012200106000E3Q00201001060006000F2Q0018010700014Q0018010800024Q008C0106000800020010560005000D00062Q007000055Q0030050005001000112Q0070000500054Q005E0105000100012Q009D000500063Q00202Q0005000500124Q00068Q00073Q00014Q000800033Q00202Q00080008001400122Q000900156Q00080002000200102Q0007001300084Q0005000700012Q0070000500063Q0020100105000500122Q0070000600044Q002A01073Q00010030050007001600172Q004D0105000700012Q0070000500073Q0006930005004200013Q00049F012Q004200012Q0070000500073Q0020110005000500182Q00040105000200012Q0070000500083Q00201001050005001900201100050005001A0006D400070001000100012Q00703Q00054Q008C0105000700022Q0095010500074Q0024012Q00013Q00023Q000A3Q00030B3Q004765745465787453697A652Q033Q0047657403073Q00746578742E756903043Q00456E756D03043Q00466F6E74030A3Q00536F7572636553616E7303073Q00566563746F72322Q033Q006E6577026Q002C40026Q00794000134Q00707Q0020115Q00012Q0070000200014Q0070000300023Q002010010300030002001291000400034Q0089000300020002001220010400043Q002010010400040005002010010400040006001220010500073Q0020100105000500082Q0070000600033Q00203E0006000600090012910007000A4Q0072010500074Q0092017Q00358Q0024012Q00017Q00033Q00030D3Q0055736572496E7075745479706503043Q00456E756D030D3Q004D6F7573654D6F76656D656E7401093Q0020C700013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q000100080001000200049F012Q000800012Q007000016Q005E2Q01000100012Q0024012Q00017Q00073Q00026Q00F03F030A3Q00446973636F2Q6E65637403053Q0054772Q656E03163Q004261636B67726F756E645472616E73706172656E637903103Q00546578745472616E73706172656E637903073Q0056697369626C65012Q001E4Q00707Q0020605Q00012Q0095017Q00703Q00013Q0006933Q000B00013Q00049F012Q000B00012Q00703Q00013Q0020115Q00022Q0004012Q000200012Q001E8Q0095012Q00014Q00703Q00023Q0006FC3Q000F0001000100049F012Q000F00012Q0024012Q00014Q00703Q00033Q002055014Q00034Q000100026Q00023Q000100302Q0002000400016Q000200016Q00033Q00206Q00034Q000100046Q00023Q000100302Q0002000500012Q004D012Q000200012Q00703Q00023Q0030053Q000600072Q0024012Q00017Q00053Q00034Q00030A3Q004D6F757365456E74657203073Q00436F2Q6E656374030A3Q004D6F7573654C6561766503043Q004769766503203Q0006933Q000600013Q00049F012Q000600010006930001000600013Q00049F012Q00060001002647000100070001000100049F012Q000700012Q0024012Q00013Q00201001033Q00020020110003000300030006D400053Q000100042Q00708Q00703Q00014Q00703Q00024Q0018012Q00014Q008C01030005000200201001043Q00040020110004000400030006D400060001000100012Q00703Q00024Q008C0104000600020006930002001C00013Q00049F012Q001C00010020110005000200052Q0015010700036Q00050007000100202Q0005000200054Q000700046Q0005000700012Q0018010500034Q0018010600044Q00B6000500034Q0024012Q00013Q00023Q00033Q00026Q00F03F03043Q007461736B03053Q0064656C6179000E4Q00A77Q00206Q00019Q009Q0000122Q000100023Q00202Q0001000100034Q000200013Q0006D400033Q000100042Q00708Q0018017Q00703Q00024Q00703Q00034Q004D2Q01000300012Q0024012Q00013Q00013Q00013Q0003043Q0053686F7700094Q00708Q0070000100013Q00066A012Q00080001000100049F012Q000800012Q00703Q00023Q002010014Q00012Q0070000100034Q0004012Q000200012Q0024012Q00017Q00013Q0003043Q004869646500044Q00707Q002010014Q00012Q005E012Q000100012Q0024012Q00017Q00023Q0003043Q0048696465030A3Q00446F436C65616E696E67000B4Q009A016Q00206Q00016Q000100016Q00013Q00206Q00026Q000200016Q00026Q000200046Q000100038Q00028Q00017Q00153Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D6503093Q00636F72652F4D61696403093Q00636F72652F44726167030D3Q00636F72652F506C6174666F726D03043Q0067616D65030A3Q0047657453657276696365030A3Q0052756E5365727669636503073Q00506C617965727303073Q002Q5F696E64657803153Q006175726F72612F77617465726D61726B2E6A736F6E2Q033Q006E657703043Q0050696E6703073Q00436F6D706F736503073Q00526566726573682Q033Q0053657403093Q005365744669656C6473030A3Q0053657456697369626C65030C3Q0053617665506F736974696F6E030F3Q00526573746F7265506F736974696F6E03073Q0044657374726F7901434Q009500015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q00050002000200122Q000600063Q00202Q00060006000700122Q000800086Q00060008000200122Q000700063Q00202Q00070007000700122Q000900096Q0007000900024Q000800086Q00095Q00102Q0009000A000900122Q000A000B3Q0006D4000B3Q000100062Q0018012Q00094Q0018012Q00034Q0018012Q00014Q0018012Q00024Q0018012Q00044Q0018012Q00063Q0010560009000C000B0006D4000B0001000100012Q0018012Q00023Q0006D4000C0002000100012Q0018012Q00023Q0006D4000D0003000100012Q0018012Q00083Q0010560009000D000D0006D4000D0004000100032Q0018012Q000B4Q0018012Q00074Q0018012Q000C3Q0010560009000E000D000290010D00053Q0010560009000F000D000290010D00063Q00105600090010000D000290010D00073Q00105600090011000D000290010D00083Q00105600090012000D0006D4000D0009000100022Q0018012Q00054Q0018012Q000A3Q00105600090013000D0006D4000D000A000100022Q0018012Q00054Q0018012Q000A3Q00105600090014000D000290010D000B3Q00105600090015000D2Q00AA010900024Q0024012Q00013Q000C3Q00403Q00030C3Q007365746D6574617461626C6503043Q004D6169642Q033Q006E657703063Q004669656C647303043Q006E616D6503043Q00757365722Q033Q0066707303043Q0070696E6703053Q00636C6F636B03053Q005469746C6503063Q006175726F726103073Q0053616D706C65732Q033Q00467073028Q0003043Q00522Q6F742Q033Q004E657703053Q004672616D6503043Q004E616D6503093Q0057617465726D61726B03083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q00304003043Q0053697A65026Q002440026Q003540030D3Q004175746F6D6174696353697A6503043Q00456E756D03013Q005803103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E03093Q00636F6C6F722E77696E03163Q004261636B67726F756E645472616E73706172656E637903093Q00616C7068612E77696E03073Q0056697369626C65010003063Q005A496E646578026Q00794003063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E63746C03063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503073Q0050612Q64696E67026Q00224003043Q004769766503053Q004C6162656C03043Q0054657874026Q00F03F030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903083Q0052696368546578742Q0103043Q006D6F6E6F03073Q004472612Q67657203063Q00412Q7461636803053Q006F6E456E64030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637403093Q0048656172746265617403073Q0052656672657368030F3Q00526573746F7265506F736974696F6E02A73Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q001220010200014Q002A01036Q007000046Q008C0102000400022Q0070000300013Q0020100103000300032Q00F20003000100020010560002000200030020100103000100040006FC000300160001000100049F012Q001600012Q002A010300053Q001291000400053Q001291000500063Q001291000600073Q001291000700083Q001291000800094Q002500030005000100105600020004000300201001030001000A0006FC0003001B0001000100049F012Q001B00010012910003000B3Q0010560002000A00032Q002A01035Q0010560002000C00030030050002000D000E2Q006B000300023Q00202Q00030003001000122Q000400116Q00053Q000900302Q00050012001300122Q000600153Q00202Q00060006001600122Q000700173Q00122Q000800176Q000600080002001056000500140006001220010600153Q002010010600060016001291000700193Q0012910008001A4Q008C0106000800020010560005001800060012200106001C3Q00201001060006001B00206801060006001D00102Q0005001B00064Q000600023Q00202Q00060006001F00122Q000700206Q00060002000200102Q0005001E00064Q000600023Q00202Q00060006001F00122Q000700224Q0089000600020002001056000500210006002010010600010023002647000600420001002400049F012Q004200012Q001200066Q0065010600013Q00105101050023000600302Q00050025002600102Q000500276Q00030005000200102Q0002000F00034Q000300023Q00202Q0003000300284Q000400033Q00202Q00040004002900122Q0005002A4Q008900040002000200209D01050002000F4Q0003000500014Q000300023Q00202Q00030003002B00202Q00040002000F00122Q0005002C3Q00122Q0006002D6Q0003000600014Q000300023Q00202Q00030003002E00201001040002000F0012910005000E3Q0012910006002F3Q0012910007000E3Q0012910008002F4Q004D01030008000100201001030002000200201100030003003000201001050002000F2Q004D0103000500012Q0070000300023Q0020100103000300322Q002A01043Q0007003005000400120032001220010500153Q0020100105000500030012910006000E3Q0012910007000E3Q001291000800333Q0012910009000E4Q008C0105000900020010560004001800050012200105001C3Q00201001050005001B00201001050005001D0010560004001B000500201001050002000A0010560004003200052Q0070000500023Q00201001050005001F001291000600354Q008900050002000200105600040034000500300500040036003700201001050002000F001056000400270005001291000500384Q008C0103000500020010560002003100032Q0070000300043Q00201001030003003A00201001040002000F00201001050002000F2Q002A01063Q00010006D400073Q000100012Q0018012Q00023Q00109B0006003B00074Q00030006000200102Q00020039000300202Q00030002000200202Q00030003003000202Q0005000200394Q00030005000100202Q00030002000200202Q0003000300304Q000500053Q00202Q00050005003C00202Q00050005003D0006D400070001000100012Q0018012Q00024Q00DE000500076Q00033Q000100122Q0003000E3Q00202Q00040002000200202Q0004000400304Q000600053Q00202Q00060006003E00202Q00060006003D0006D400080002000100022Q0018012Q00034Q0018012Q00024Q0072010600084Q006101043Q000100201100040002003F2Q00040104000200010020110004000200402Q00040104000200012Q00AA010200024Q0024012Q00013Q00033Q00013Q00030C3Q0053617665506F736974696F6E00044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00083Q0003043Q007469636B03053Q007461626C6503063Q00696E7365727403073Q0053616D706C6573028Q00026Q00F03F03063Q0072656D6F76652Q033Q0046707300203Q001220012Q00014Q00F23Q000100020012202Q0100023Q00207C0001000100034Q00025Q00202Q0002000200044Q00038Q0001000300012Q007000015Q0020102Q01000100042Q0001000100013Q000EC80005001A0001000100049F012Q001A00012Q007000015Q0020102Q01000100040020102Q010001000600203E00023Q000600061A2Q01001A0001000200049F012Q001A00010012202Q0100023Q0020102Q01000100072Q007000025Q002010010200020004001291000300064Q004D2Q010003000100049F012Q000800012Q007000016Q007000025Q0020100102000200042Q0001000200023Q0010560001000800022Q0024012Q00017Q00033Q00026Q00F03F028Q0003073Q0052656672657368010C4Q001800018Q000100016Q00018Q00015Q000E2Q0001000B0001000100049F012Q000B0001001291000100024Q00952Q016Q0070000100013Q0020110001000100032Q00042Q01000200012Q0024012Q00017Q00083Q002Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403063Q00737472696E6703063Q00666F726D6174030C3Q0025303258253032582530325803013Q005203013Q004703013Q004200144Q00707Q002010014Q0001001291000100024Q00893Q000200020002902Q015Q00120D010200033Q00202Q00020002000400122Q000300056Q000400013Q00202Q00053Q00064Q0004000200024Q000500013Q00202Q00063Q00074Q0005000200024Q000600013Q00201001073Q00082Q00F6000600074Q009201026Q003500026Q0024012Q00013Q00013Q00083Q0003043Q006D61746803053Q00666C2Q6F722Q033Q006D6178028Q002Q033Q006D696E026Q00F03F025Q00E06F40026Q00E03F01103Q00128F000100013Q00202Q00010001000200122Q000200013Q00202Q00020002000300122Q000300043Q00122Q000400013Q00202Q00040004000500122Q000500066Q00068Q000400064Q007301023Q000200208A01020002000700202Q0002000200084Q000100026Q00019Q0000017Q00083Q002Q033Q0047657403083Q00636F6C6F722E6C6F03063Q00737472696E6703063Q00666F726D617403253Q003C666F6E7420636F6C6F723D2223253032582530325825303258223E25733C2F666F6E743E03013Q005203013Q004703013Q004201154Q007000015Q0020102Q0100010001001291000200024Q008900010002000200029001025Q00120D010300033Q00202Q00030003000400122Q000400056Q000500023Q00202Q0006000100064Q0005000200024Q000600023Q00202Q0007000100074Q0006000200024Q000700023Q0020100108000100082Q00890007000200022Q001801086Q0056010300084Q003500036Q0024012Q00013Q00013Q00083Q0003043Q006D61746803053Q00666C2Q6F722Q033Q006D6178028Q002Q033Q006D696E026Q00F03F025Q00E06F40026Q00E03F01103Q00128F000100013Q00202Q00010001000200122Q000200013Q00202Q00020002000300122Q000300043Q00122Q000400013Q00202Q00040004000500122Q000500066Q00068Q000400064Q007301023Q000200208A01020002000700202Q0002000200084Q000100026Q00019Q0000017Q00043Q0003053Q007063612Q6C028Q0003043Q006D61746803053Q00666C2Q6F7201224Q007000015Q0006FC0001000C0001000100049F012Q000C00010012202Q0100013Q00029001026Q005E0001000200020006930001000A00013Q00049F012Q000A000100060B0103000B0001000200049F012Q000B00012Q006501036Q009501036Q007000015Q0006FC000100110001000100049F012Q00110001001291000100024Q00AA2Q0100023Q0012202Q0100013Q0006D400020001000100012Q00708Q005E0001000200020006930001001F00013Q00049F012Q001F00010006930002001F00013Q00049F012Q001F0001001220010300033Q0020100103000300042Q0018010400024Q00890003000200020006FC000300200001000100049F012Q00200001001291000300024Q00AA010300024Q0024012Q00013Q00023Q00033Q0003043Q0067616D65030A3Q004765745365727669636503053Q00537461747300063Q001220012Q00013Q0020035Q000200122Q000200038Q00029Q008Q00017Q00043Q0003073Q004E6574776F726B030F3Q0053657276657253746174734974656D03093Q00446174612050696E6703083Q0047657456616C756500084Q0088016Q00206Q000100206Q000200206Q000300206Q00046Q00019Q008Q00017Q001E3Q0003063Q0069706169727303063Q004669656C647303043Q006E616D65026Q00F03F03063Q00737472696E6703063Q00666F726D6174031B3Q003C666F6E7420636F6C6F723D22232573223E25733C2F666F6E743E03053Q005469746C6503043Q0075736572030B3Q004C6F63616C506C6179657203043Q004E616D6503063Q00706C617965722Q033Q006670732Q033Q0046707303043Q002066707303043Q0070696E6703043Q0050696E672Q033Q00206D7303053Q00636C6F636B03023Q006F7303043Q006461746503083Q0025483A254D3A255303043Q007479706503083Q0066756E6374696F6E03053Q007063612Q6C03083Q00746F737472696E6703053Q007461626C6503063Q00636F6E63617403013Q002003013Q007C01644Q00322Q015Q00122Q000200013Q00202Q00033Q00024Q00020002000400044Q00560001002647000600120001000300049F012Q001200012Q0001000700013Q002060000700070004001220010800053Q002010010800080006001291000900074Q0070000A6Q00F2000A00010002002010010B3Q00082Q008C0108000B00022Q004A2Q010007000800049F012Q00560001002647000600200001000900049F012Q002000012Q0070000700013Q00201001070007000A2Q0001000800013Q0020600008000800040006930007001D00013Q00049F012Q001D000100201001090007000B0006FC0009001E0001000100049F012Q001E00010012910009000C4Q004A2Q010008000900049F012Q00560001002647000600290001000D00049F012Q002900012Q0001000700013Q00206000070007000400201001083Q000E0012910009000F4Q006B0108000800092Q004A2Q010007000800049F012Q00560001002647000600330001001000049F012Q003300012Q0001000700013Q00206000070007000400201100083Q00112Q0089000800020002001291000900124Q006B0108000800092Q004A2Q010007000800049F012Q005600010026470006003D0001001300049F012Q003D00012Q0001000700013Q002060000700070004001220010800143Q002010010800080015001291000900164Q00890008000200022Q004A2Q010007000800049F012Q00560001001220010700174Q0018010800064Q0089000700020002002647000700500001001800049F012Q00500001001220010700194Q0018010800064Q005E0007000200080006930007005600013Q00049F012Q005600010006930008005600013Q00049F012Q005600012Q0001000900013Q00209801090009000400122Q000A001A6Q000B00086Q000A000200024Q00010009000A00044Q005600012Q0001000700013Q00201B01070007000400122Q0008001A6Q000900066Q0008000200024Q000100070008000677000200050001000200049F012Q000500010012200102001B3Q00201001020002001C2Q0018010300013Q0012910004001D4Q0070000500023Q0012910006001E4Q00890005000200020012910006001D4Q006B0104000400062Q0056010200044Q003500026Q0024012Q00017Q00043Q0003053Q004C6162656C03063Q00506172656E7403043Q005465787403073Q00436F6D706F7365010E3Q0020102Q013Q00010006930001000700013Q00049F012Q000700010020102Q013Q00010020102Q01000100020006FC000100080001000100049F012Q000800012Q0024012Q00013Q0020102Q013Q000100201100023Q00042Q00890002000200020010560001000300022Q00AA012Q00024Q0024012Q00017Q00033Q0003053Q004C6162656C03043Q005465787403083Q00746F737472696E6702073Q00201001023Q0001001220010300034Q0018010400014Q00890003000200020010560002000200032Q00AA012Q00024Q0024012Q00017Q00023Q0003063Q004669656C647303073Q005265667265736802083Q00060B010200030001000100049F012Q000300012Q002A01025Q0010563Q0001000200201100023Q00022Q0056010200034Q003500026Q0024012Q00017Q00023Q0003043Q00522Q6F7403073Q0056697369626C65020A3Q00201001023Q00010006930001000600013Q00049F012Q000600012Q0065010300013Q0006FC000300070001000100049F012Q000700012Q006501035Q0010560002000200032Q00AA012Q00024Q0024012Q00017Q00033Q0003053Q007063612Q6C03073Q0053746F7261676503053Q005772697465010D3Q0012202Q0100013Q0006D400023Q000100012Q0018017Q005E0001000200020006930001000C00013Q00049F012Q000C00012Q007000035Q00207401030003000200202Q0003000300034Q000400016Q000500026Q0003000500012Q0024012Q00013Q00013Q000B3Q0003043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q747053657276696365030A3Q004A534F4E456E636F646503013Q007803043Q00522Q6F7403083Q00506F736974696F6E03013Q005803063Q004F2Q6673657403013Q007903013Q005900153Q0012C33Q00013Q00206Q000200122Q000200038Q0002000200206Q00044Q00023Q00024Q00035Q00202Q00030003000600202Q00030003000700202Q0003000300080020100103000300090010560002000500032Q007000035Q00201001030003000600201001030003000700201001030003000B0020100103000300090010560002000A00032Q0056012Q00024Q00358Q0024012Q00017Q000C3Q0003073Q0053746F7261676503043Q005265616403053Q007063612Q6C03043Q007479706503053Q007461626C6503013Q007803043Q00522Q6F7403083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q6673657403013Q0079026Q00304001214Q006900015Q00202Q00010001000100202Q0001000100024Q000200016Q00010002000200062Q000100080001000100049F012Q000800012Q0024012Q00013Q001220010200033Q0006D400033Q000100012Q0018012Q00014Q005E0002000200030006930002002000013Q00049F012Q00200001001220010400044Q0018010500034Q0089000400020002002647000400200001000500049F012Q002000010020100104000300060006930004002000013Q00049F012Q0020000100201001043Q0007001220010500093Q00201001050005000A00201001060003000600201001070003000B0006FC0007001E0001000100049F012Q001E00010012910007000C4Q008C0105000700020010560004000800052Q0024012Q00013Q00013Q00043Q0003043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q747053657276696365030A3Q004A534F4E4465636F646500093Q001220012Q00013Q0020115Q0002001291000200034Q008C012Q000200020020115Q00042Q007000026Q0056012Q00024Q00358Q0024012Q00017Q00023Q0003043Q004D616964030A3Q00446F436C65616E696E6701043Q0020102Q013Q00010020110001000100022Q00042Q01000200012Q0024012Q00017Q00133Q00030C3Q00636F72652F43726561746F72030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E03093Q00636F72652F4D61696403093Q00636F72652F44726167030A3Q00636F72652F466C616773030D3Q00636F72652F506C6174666F726D03143Q00636F6D706F6E656E74732F4B65795069636B657203073Q002Q5F696E646578026Q006340026Q00314003143Q006175726F72612F6B657962696E64732E6A736F6E2Q033Q006E657703043Q004C69766503073Q0052656672657368030A3Q0053657456697369626C65030C3Q0053617665506F736974696F6E030F3Q00526573746F7265506F736974696F6E03073Q0044657374726F79013E4Q00092Q015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q00122Q000500046Q0004000200024Q00055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q00122Q000900086Q0008000200024Q00095Q00102Q00090009000900122Q000A000A3Q00122Q000B000B3Q00122Q000C000C3Q0006D4000D3Q000100072Q0018012Q00094Q0018012Q00044Q0018012Q00014Q0018012Q000A4Q0018012Q00024Q0018012Q00054Q0018012Q00063Q0010560009000D000D0006D4000D0001000100012Q0018012Q00083Q0010560009000E000D0006D4000D0002000100052Q0018012Q00014Q0018012Q000B4Q0018012Q000A4Q0018012Q00024Q0018012Q00033Q0010560009000F000D000290010D00033Q00105600090010000D0006D4000D0004000100022Q0018012Q00074Q0018012Q000C3Q00105600090011000D0006D4000D0005000100022Q0018012Q00074Q0018012Q000C3Q00105600090012000D000290010D00063Q00105600090013000D2Q00AA010900024Q0024012Q00013Q00073Q003E3Q00030C3Q007365746D6574617461626C6503043Q004D6169642Q033Q006E657703043Q00526F777303043Q00522Q6F742Q033Q004E657703053Q004672616D6503043Q004E616D6503083Q004B657962696E647303083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q003040026Q00474003043Q0053697A65026Q00354003103Q004261636B67726F756E64436F6C6F723303053Q00546F6B656E03093Q00636F6C6F722E77696E03163Q004261636B67726F756E645472616E73706172656E637903093Q00616C7068612E77696E03073Q0056697369626C65010003103Q00436C69707344657363656E64616E74732Q0103063Q005A496E646578026Q00794003063Q00506172656E7403063Q00436F726E65722Q033Q00476574030A3Q007261646975732E626F7803063Q005374726F6B65030B3Q00636F6C6F722E7768697465030A3Q00616C7068612E6C696E6503043Q004769766503063Q00486561646572026Q00F03F028Q0003043Q0054657874026Q002040026Q0030C003053Q005469746C6503083Q006B657962696E6473030A3Q0054657874436F6C6F723303083Q00636F6C6F722E686903053Q00736D612Q6C03093Q00556E6465726C696E65030B3Q00416E63686F72506F696E7403073Q00566563746F7232030E3Q00616C7068612E6C696E65536F667403043Q00426F6479026Q0035C003073Q0050612Q64696E67026Q00084003043Q004C69737403073Q004472612Q67657203063Q00412Q7461636803053Q006F6E456E6403073Q004368616E67656403073Q00436F2Q6E65637403073Q0052656672657368030F3Q00526573746F7265506F736974696F6E02E13Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100023Q001220010200014Q007001038Q00048Q0002000400024Q000300013Q00202Q0003000300034Q00030001000200102Q0002000200034Q00035Q00102Q0002000400034Q000300023Q00202Q00030003000600122Q000400076Q00053Q000900302Q00050008000900122Q0006000B3Q00202Q00060006000C00122Q0007000D3Q00122Q0008000E6Q00060008000200102Q0005000A000600122Q0006000B3Q00202Q00060006000C4Q000700033Q00122Q000800106Q00060008000200102Q0005000F00064Q000600023Q00202Q00060006001200122Q000700136Q00060002000200102Q0005001100064Q000600023Q00202Q00060006001200122Q000700156Q00060002000200102Q00050014000600202Q00060001001600262Q0006002D0001001700049F012Q002D00012Q001200066Q0065010600013Q0010F500050016000600302Q00050018001900302Q0005001A001B00102Q0005001C6Q00030005000200102Q0002000500034Q000300023Q00202Q00030003001D4Q000400043Q00202Q00040004001E00122Q0005001F6Q00040002000200202Q0005000200054Q0003000500014Q000300023Q00202Q00030003002000202Q00040002000500122Q000500213Q00122Q000600226Q00030006000100202Q00030002000200202Q00030003002300202Q0005000200054Q0003000500014Q000300023Q00202Q00030003000600122Q000400076Q00053Q000400302Q00050008002400122Q0006000B3Q00202Q00060006000300122Q000700253Q00122Q000800263Q00122Q000900263Q00122Q000A00106Q0006000A000200102Q0005000F000600302Q00050014002500202Q00060002000500102Q0005001C00064Q00030005000200102Q0002002400034Q000300023Q00202Q0003000300274Q00043Q000500122Q0005000B3Q00202Q00050005000C00122Q000600283Q00122Q000700266Q00050007000200102Q0004000A000500122Q0005000B3Q00202Q00050005000300122Q000600253Q00122Q000700293Q00122Q000800253Q00122Q000900266Q00050009000200102Q0004000F000500202Q00050001002A00062Q0005006D0001000100049F012Q006D00010012910005002B3Q0010560004002700052Q0070000500023Q0020100105000500120012910006002D4Q00890005000200020010560004002C00050020100105000200240010560004001C00050012910005002E4Q004D0103000500012Q0070000300023Q0020100103000300060012DF000400076Q00053Q000600122Q000600313Q00202Q00060006000300122Q000700263Q00122Q000800256Q00060008000200102Q00050030000600122Q0006000B3Q00202Q000600060003001291000700263Q001242010800263Q00122Q000900253Q00122Q000A00266Q0006000A000200102Q0005000A000600122Q0006000B3Q00202Q00060006000300122Q000700253Q00122Q000800263Q00122Q000900263Q001291000A00254Q008C0106000A00020010560005000F00062Q0070000600023Q002010010600060012001291000700214Q00890006000200020010560005001100062Q0070000600023Q002010010600060012001291000700324Q008900060002000200105200050014000600202Q00060002002400102Q0005001C00064Q00030005000200102Q0002002F00034Q000300023Q00202Q00030003000600122Q000400076Q00053Q000500302Q0005000800330012200106000B3Q00201001060006000C001291000700263Q0012E5000800106Q00060008000200102Q0005000A000600122Q0006000B3Q00202Q00060006000300122Q000700253Q00122Q000800263Q00122Q000900253Q00122Q000A00346Q0006000A00020010560005000F00060030050005001400250020100106000200050010560005001C00062Q008C0103000500020010560002003300032Q0070000300023Q002010010300030035002010010400020033001291000500363Q001291000600363Q001291000700363Q001291000800364Q004D0103000800012Q0070000300023Q002010010300030037002010010400020033001291000500264Q004D0103000500012Q0070000300053Q0020100103000300390020100104000200240020100105000200052Q002A01063Q00010006D400073Q000100012Q0018012Q00023Q00109B0006003A00074Q00030006000200102Q00020038000300202Q00030002000200202Q00030003002300202Q0005000200384Q00030005000100202Q00030002000200202Q0003000300234Q000500063Q00202Q00050005003B00202Q00050005003C0006D400070001000100012Q0018012Q00024Q0072010500074Q006101033Q000100201100030002003D2Q000401030002000100201100030002003E2Q00040103000200012Q00AA010200024Q0024012Q00013Q00023Q00013Q00030C3Q0053617665506F736974696F6E00044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q00013Q0003073Q005265667265736800044Q00707Q0020115Q00012Q0004012Q000200012Q0024012Q00017Q000B3Q0003083Q005265676973747279026Q00F03F026Q00F0BF03063Q0042752Q746F6E0003063Q00506172656E7403053Q007461626C6503063Q0072656D6F766503063Q006970616972732Q033Q004B657903043Q004E6F5549012E4Q002A2Q016Q007000025Q0020100102000200012Q0001000200023Q001291000300023Q001291000400033Q0004F30002001C00012Q007000065Q0020100106000600012Q0016010600060005002010010700060004002696000700110001000500049F012Q00110001002010010700060004002010010700070006002647000700120001000500049F012Q001200012Q001200076Q0065010700013Q0006FC0007001B0001000100049F012Q001B0001001220010800073Q00207C0008000800084Q00095Q00202Q0009000900014Q000A00056Q0008000A0001000451000200070001001220010200094Q007000035Q0020100103000300012Q005E00020002000400049F012Q002A000100201001070006000A0026960007002A0001000500049F012Q002A000100201001070006000B0006FC0007002A0001000100049F012Q002A00012Q0001000700013Q0020600007000700022Q004A2Q0100070006000677000200210001000200049F012Q002100012Q00AA2Q0100024Q0024012Q00017Q003D3Q0003043Q00426F647903063Q00506172656E7403063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103093Q004775694F626A65637403073Q0044657374726F7903043Q00526F777303043Q004C697665028Q0003043Q005465787403043Q004E616D6503053Q00456D70747903043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F03083Q006E6F2062696E6473030A3Q0054657874436F6C6F723303053Q00546F6B656E03083Q00636F6C6F722E6C6F030E3Q005465787458416C69676E6D656E7403043Q00456E756D03063Q0043656E74657203053Q00736D612Q6C03043Q00522Q6F74030A3Q0066726F6D4F2Q66736574026Q003540026Q00184003083Q0047657453746174652Q033Q004E657703053Q004672616D6503053Q004C6162656C03103Q004261636B67726F756E64436F6C6F7233030C3Q00636F6C6F722E612Q63656E7403163Q004261636B67726F756E645472616E73706172656E637902C3F5285C8FC2ED3F030B3Q004C61796F75744F7264657203063Q00436F726E6572026Q00084003083Q00506F736974696F6E026Q001440025Q008051C02Q033Q0047657403093Q00636F6C6F722E6D6964030C3Q00546578745472756E6361746503053Q004174456E642Q033Q004B6579030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q0014C0026Q004F4003013Q005B03073Q004B65794E616D6503023Q005D2003043Q004D6F646503053Q006C6F77657203053Q00526967687403043Q006D6F6E6F03063Q005069636B657203053Q0054772Q656E01E33Q0020102Q013Q00010006930001000700013Q00049F012Q000700010020102Q013Q00010020102Q01000100020006FC000100080001000100049F012Q000800012Q0024012Q00013Q0012202Q0100033Q00201001023Q00010020110002000200042Q00F6000200034Q00A42Q013Q000300049F012Q00150001002011000600050005001291000800064Q008C0106000800020006930006001500013Q00049F012Q001500010020110006000500072Q00040106000200010006770001000E0001000200049F012Q000E00012Q002A2Q015Q00102D012Q0008000100202Q00013Q00094Q0001000200024Q000200013Q00262Q000200420001000A00049F012Q004200012Q007000025Q00207200020002000B4Q00033Q000600302Q0003000C000D00122Q0004000F3Q00202Q00040004001000122Q000500113Q00122Q0006000A3Q00122Q0007000A6Q000800016Q00040008000200102Q0003000E000400302Q0003000B00124Q00045Q00202Q00040004001400122Q000500156Q00040002000200102Q00030013000400122Q000400173Q00202Q00040004001600202Q00040004001800102Q00030016000400202Q00043Q000100102Q00030002000400122Q000400196Q00020004000100202Q00023Q001A00122Q0003000F3Q00202Q00030003001B4Q000400026Q000500013Q00102Q0005001C000500202Q00050005001D4Q00030005000200102Q0002000E00036Q00023Q001220010200034Q0018010300014Q005E00020002000400049F012Q00D0000100201100070006001E2Q00230007000200024Q00085Q00202Q00080008001F00122Q000900206Q000A3Q000600202Q000B0006002100102Q000A000C000B00122Q000B000F3Q00202Q000B000B001000122Q000C00113Q00122Q000D000A3Q00122Q000E000A6Q000F00016Q000B000F000200102Q000A000E000B4Q000B5Q00202Q000B000B001400122Q000C00236Q000B0002000200102Q000A0022000B00062Q0007006000013Q00049F012Q00600001001291000B00253Q0006FC000B00610001000100049F012Q00610001001291000B00113Q001056000A0024000B001085000A0026000500202Q000B3Q000100102Q000A0002000B4Q0008000A00024Q00095Q00202Q00090009002700122Q000A00286Q000B00086Q0009000B00014Q00095Q00201001090009000B2Q002A010A3Q00070030B3000A000C002100122Q000B000F3Q00202Q000B000B001B00122Q000C002A3Q00122Q000D000A6Q000B000D000200102Q000A0029000B00122Q000B000F3Q00202Q000B000B001000122Q000C00113Q0012C5000D002B3Q00122Q000E00113Q00122Q000F000A6Q000B000F000200102Q000A000E000B00202Q000B0006002100102Q000A000B000B00062Q0007008700013Q00049F012Q008700012Q0070000B00033Q002010010B000B002C001291000C00234Q0089000B000200020006FC000B008B0001000100049F012Q008B00012Q0070000B00033Q002010010B000B002C001291000C002D4Q0089000B00020002001056000A0013000B001220010B00173Q002010010B000B002E002010010B000B002F001056000A002E000B001056000A000200080012EA000B00196Q0009000B00014Q00095Q00202Q00090009000B4Q000A3Q000800302Q000A000C003000122Q000B00323Q00202Q000B000B001000122Q000C00113Q00122Q000D000A4Q008C010B000D0002001056000A0031000B001220010B000F3Q002010010B000B0010001291000C00113Q001291000D00333Q001291000E000A3Q001291000F000A4Q008C010B000F0002001056000A0029000B001220010B000F3Q002010010B000B001B001291000C00344Q0070000D00014Q008C010B000D0002001056000A000E000B001291000B00353Q002011000C000600362Q0089000C00020002001291000D00373Q002010010E00060038002011000E000E00392Q0089000E000200022Q006B010B000B000E001056000A000B000B000693000700BC00013Q00049F012Q00BC00012Q0070000B00033Q002010010B000B002C001291000C00234Q0089000B000200020006FC000B00C00001000100049F012Q00C000012Q0070000B00033Q002010010B000B002C001291000C00154Q0089000B00020002001056000A0013000B0012B2000B00173Q00202Q000B000B001600202Q000B000B003A00102Q000A0016000B00102Q000A0002000800122Q000B003B6Q0009000B000100202Q00093Q000800202Q000A3Q00084Q000A000A3Q00202Q000A000A00114Q000B3Q000200102Q000B001A000800102Q000B003C00064Q0009000A000B000677000200460001000200049F012Q004600012Q0070000200043Q00201001020002003D00201001033Q001A2Q002A01043Q00010012200105000F3Q00201001050005001B2Q0070000600024Q0001000700014Q0070000800014Q003601070007000800103D0007001C000700206000070007001D2Q008C0105000700020010560004000E00052Q004D0102000400012Q00AA012Q00024Q0024012Q00017Q00023Q0003043Q00522Q6F7403073Q0056697369626C65020A3Q00201001023Q00010006930001000600013Q00049F012Q000600012Q0065010300013Q0006FC000300070001000100049F012Q000700012Q006501035Q0010560002000200032Q00AA012Q00024Q0024012Q00017Q00033Q0003053Q007063612Q6C03073Q0053746F7261676503053Q005772697465010D3Q0012202Q0100013Q0006D400023Q000100012Q0018017Q005E0001000200020006930001000C00013Q00049F012Q000C00012Q007000035Q00207401030003000200202Q0003000300034Q000400016Q000500026Q0003000500012Q0024012Q00013Q00013Q000B3Q0003043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q747053657276696365030A3Q004A534F4E456E636F646503013Q007803043Q00522Q6F7403083Q00506F736974696F6E03013Q005803063Q004F2Q6673657403013Q007903013Q005900153Q0012C33Q00013Q00206Q000200122Q000200038Q0002000200206Q00044Q00023Q00024Q00035Q00202Q00030003000600202Q00030003000700202Q0003000300080020100103000300090010560002000500032Q007000035Q00201001030003000600201001030003000700201001030003000B0020100103000300090010560002000A00032Q0056012Q00024Q00358Q0024012Q00017Q000C3Q0003073Q0053746F7261676503043Q005265616403053Q007063612Q6C03043Q007479706503053Q007461626C6503013Q007803043Q00522Q6F7403083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q6673657403013Q0079026Q00474001214Q006900015Q00202Q00010001000100202Q0001000100024Q000200016Q00010002000200062Q000100080001000100049F012Q000800012Q0024012Q00013Q001220010200033Q0006D400033Q000100012Q0018012Q00014Q005E0002000200030006930002002000013Q00049F012Q00200001001220010400044Q0018010500034Q0089000400020002002647000400200001000500049F012Q002000010020100104000300060006930004002000013Q00049F012Q0020000100201001043Q0007001220010500093Q00201001050005000A00201001060003000600201001070003000B0006FC0007001E0001000100049F012Q001E00010012910007000C4Q008C0105000700020010560004000800052Q0024012Q00013Q00013Q00043Q0003043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q747053657276696365030A3Q004A534F4E4465636F646500093Q001220012Q00013Q0020115Q0002001291000200034Q008C012Q000200020020115Q00042Q007000026Q0056012Q00024Q00358Q0024012Q00017Q00033Q0003043Q004D616964030A3Q00446F436C65616E696E6703043Q00526F777301063Q0020892Q013Q000100202Q0001000100024Q0001000200014Q00015Q00104Q000300016Q00017Q000A3Q0003093Q00636F72652F5574696C030B3Q00636F72652F486F746B657903093Q00636F72652F4D61696403073Q002Q5F696E6465782Q033Q006E657703073Q004361707475726503073Q00526573746F726503083Q00536574517565727903053Q00436C65617203073Q0044657374726F79011F4Q00182Q015Q001291000200014Q00890001000200022Q001801025Q001291000300024Q00890002000200022Q001801035Q001291000400034Q00890003000200022Q002A01045Q0010560004000400040006D400053Q000100032Q0018012Q00044Q0018012Q00034Q0018012Q00023Q001056000400050005000290010500013Q001056000400060005000290010500023Q001056000400070005000290010500033Q0006D400060004000100022Q0018012Q00014Q0018012Q00053Q001056000400080006000290010600053Q001056000400090006000290010600063Q0010560004000A00062Q00AA010400024Q0024012Q00013Q00073Q00113Q00030C3Q007365746D6574617461626C6503063Q0057696E646F7703043Q004D6169642Q033Q006E657703053Q005175657279034Q0003063Q00416374697665010003083Q00536E617073686F740003093Q00536561726368426F7803043Q004769766503073Q00466F637573656403073Q00436F2Q6E65637403093Q00466F6375734C6F737403183Q0047657450726F70657274794368616E6765645369676E616C03043Q0054657874012A3Q0012202Q0100014Q002A01026Q007000036Q008C2Q0100030002001056000100024Q0070000200013Q0020100102000200042Q00F200020001000200105600010003000200300500010005000600300500010007000800308C00010009000A00202Q00023Q000B00202Q00030001000300202Q00030003000C00202Q00050002000D00202Q00050005000E0006D400073Q000100012Q00703Q00024Q0072010500074Q006101033Q000100201001030001000300201100030003000C00201001050002000F00201100050005000E0006D400070001000100012Q00703Q00024Q0083010500076Q00033Q000100202Q00030001000300202Q00030003000C00202Q00050002001000122Q000700116Q00050007000200202Q00050005000E0006D400070002000100022Q0018012Q00014Q0018012Q00024Q0072010500074Q006101033Q00012Q00AA2Q0100024Q0024012Q00013Q00033Q00013Q00030D3Q0053657453752Q7072652Q73656400054Q00707Q002010014Q00012Q00652Q0100014Q0004012Q000200012Q0024012Q00017Q00013Q00030D3Q0053657453752Q7072652Q73656400054Q00707Q002010014Q00012Q00652Q016Q0004012Q000200012Q0024012Q00017Q00023Q0003083Q00536574517565727903043Q005465787400064Q00AA7Q00206Q00014Q000200013Q00202Q0002000200026Q000200016Q00017Q000E3Q0003043Q00726F777303053Q00626F78657303063Q0069706169727303063Q0057696E646F7703043Q00526F77732Q033Q00526F7703043Q00522Q6F7403073Q0056697369626C6503043Q005461627303053Q00426F78657303073Q0076697369626C6503093Q00636F2Q6C617073656403093Q00436F2Q6C617073656403083Q00536E617073686F7401294Q002A2Q013Q00022Q002A01025Q0010560001000100022Q002A01025Q001056000100020002001220010200033Q00201001033Q00040020100103000300052Q005E00020002000400049F012Q001000010020100107000100010020100108000600060020100109000600060020100109000900070020100109000900082Q004A0107000800090006770002000A0001000200049F012Q000A0001001220010200033Q00201001033Q00040020100103000300092Q005E00020002000400049F012Q00250001001220010700033Q00201001080006000A2Q005E00070002000900049F012Q00230001002010010C000100022Q002A010D3Q0002002010010E000B0007002010010E000E0008001056000D000B000E002010010E000B000D001056000D000C000E2Q004A010C000B000D0006770007001B0001000200049F012Q001B0001000677000200170001000200049F012Q001700010010563Q000E00012Q0024012Q00017Q00123Q0003083Q00536E617073686F7403053Q00706169727303043Q00726F777303043Q00522Q6F7403073Q0056697369626C6503053Q00626F78657303073Q0076697369626C6503093Q00436F2Q6C617073656403093Q00636F2Q6C6170736564030C3Q00536574436F2Q6C617073656403073Q005265667265736803063Q0069706169727303063Q0057696E646F7703043Q0054616273030D3Q005365744D61746368436F756E740003063Q004163746976650100012F3Q0020102Q013Q00010006FC000100040001000100049F012Q000400012Q0024012Q00013Q0012202Q0100023Q00201001023Q00010020100102000200032Q005E00010002000300049F012Q000B0001002010010600040004001056000600050005000677000100090001000200049F012Q000900010012202Q0100023Q00201001023Q00010020100102000200062Q005E00010002000300049F012Q0020000100201001060004000400202200070005000700102Q00060005000700202Q00060004000800202Q00070005000900062Q0006001E0001000700049F012Q001E000100201100060004000A0020100108000500092Q0065010900014Q004D01060009000100049F012Q0020000100201100060004000B2Q0004010600020001000677000100120001000200049F012Q001200010012202Q01000C3Q00201001023Q000D00201001020002000E2Q005E00010002000300049F012Q002A000100201100060005000F2Q001E000800084Q004D010600080001000677000100270001000200049F012Q002700010030053Q000100100030053Q001100122Q0024012Q00017Q00083Q002Q033Q00526F7703043Q0054657874034Q0003083Q00746F737472696E6703013Q002003083Q0047726F7570626F7803053Q005469746C6503053Q006C6F77657201153Q0020102Q013Q00010020102Q01000100020006FC000100050001000100049F012Q00050001001291000100033Q001220010200044Q0069010300016Q00020002000200122Q000300053Q00122Q000400043Q00202Q00053Q000600202Q00050005000700062Q0005000F0001000100049F012Q000F0001001291000500034Q00890004000200022Q000501020002000400202Q0002000200084Q000200036Q00029Q0000017Q001C3Q0003083Q00746F737472696E67034Q0003043Q006773756203043Q005E25732B03043Q0025732B2403053Q00517565727903073Q00526573746F726503063Q0041637469766503073Q00436170747572652Q0103053Q006C6F77657203063Q0069706169727303063Q0057696E646F7703043Q00526F777303053Q0066752Q7A79002Q033Q00526F7703043Q00522Q6F7403073Q0056697369626C6503043Q0054616273028Q0003053Q00426F786573026Q00F03F03093Q00436F2Q6C6170736564030C3Q00536574436F2Q6C617073656403083Q0053656C656374656403073Q0052656672657368030D3Q005365744D61746368436F756E7402643Q001220010200013Q00060B010300040001000100049F012Q00040001001291000300024Q008900020002000200202C01020002000300122Q000400043Q00122Q000500026Q00020005000200202Q00020002000300122Q000400053Q00122Q000500026Q0002000500024Q000100023Q00104Q0006000100262Q000100140001000200049F012Q0014000100201100023Q00072Q00040102000200012Q00AA012Q00023Q00201001023Q00080006FC0002001A0001000100049F012Q001A000100201100023Q00092Q00040102000200010030053Q0008000A00201100020001000B2Q00890002000200020012200103000C3Q00201001043Q000D00201001040004000E2Q005E00030002000500049F012Q002F00012Q007000085Q00201001080008000F2Q0018010900024Q0070000A00014Q0018010B00074Q00F6000A000B4Q007301083Q00020026470008002B0001001000049F012Q002B00012Q001200086Q0065010800013Q002010010900070011002010010900090012001056000900130008000677000300210001000200049F012Q002100010012200103000C3Q00201001043Q000D0020100104000400142Q005E00030002000500049F012Q00600001001291000800153Q0012200109000C3Q002010010A000700162Q005E00090002000B00049F012Q005B0001001291000E00153Q001220010F000C3Q0020100110000D000E2Q005E000F0002001100049F012Q004500010020100114001300120020100114001400130006930014004500013Q00049F012Q00450001002060000E000E0017000677000F00400001000200049F012Q00400001000EC8001500500001000E00049F012Q00500001002010010F000D0018000693000F005000013Q00049F012Q00500001002011000F000D00192Q006501116Q0065011200014Q004D010F00120001002010010F000D0012000EC8001500550001000E00049F012Q0055000100201001100007001A00049F012Q005700012Q001200106Q0065011000013Q001056000F00130010002011000F000D001B2Q0004010F000200012Q009E01080008000E0006770009003B0001000200049F012Q003B000100201100090007001C2Q0018010B00084Q004D0109000B0001000677000300360001000200049F012Q003600012Q00AA012Q00024Q0024012Q00017Q00053Q0003063Q0057696E646F7703093Q00536561726368426F7803043Q0054657874034Q0003073Q00526573746F726501073Q0020102Q013Q00010020102Q010001000200300500010003000400201100013Q00052Q00042Q01000200012Q00AA012Q00024Q0024012Q00017Q00033Q0003073Q00526573746F726503043Q004D616964030A3Q00446F436C65616E696E6701063Q00208B2Q013Q00014Q00010002000100202Q00013Q000200202Q0001000100034Q0001000200016Q00017Q001A3Q00030A3Q00636F72652F466C61677303093Q00636F72652F5574696C030D3Q00636F72652F506C6174666F726D03043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q74705365727669636503073Q002Q5F696E646578026Q00F03F2Q033Q006E657703093Q00536574466F6C64657203103Q0053657449676E6F7265496E6465786573030B3Q0049676E6F7265496E646578030C3Q00436F6E666967466F6C64657203073Q0050617468466F72030C3Q0053652Q74696E67735061746803073Q00436F2Q6C65637403043Q005361766503043Q004C6F616403063Q0044656C65746503043Q004C69737403083Q0053652Q74696E6773030D3Q00577269746553652Q74696E6773030B3Q005365744175746F6C6F6164030B3Q004765744175746F6C6F616403123Q004C6F61644175746F6C6F6164436F6E66696703123Q004275696C64436F6E66696753656374696F6E01494Q009900015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q00030002000200122Q000400043Q002011000400040005001291000600064Q008C0104000600022Q002A01055Q001056000500070005001291000600083Q0006D400073Q000100012Q0018012Q00053Q001056000500090007000290010700013Q0010560005000A0007000290010700023Q0010560005000B0007000290010700033Q0010560005000C00070006D400070004000100012Q0018012Q00033Q0010560005000D0007000290010700053Q0010560005000E0007000290010700063Q0010560005000F0007000290010700073Q000290010800083Q0006D400090009000100022Q0018012Q00014Q0018012Q00073Q0010560005001000090006D40009000A000100032Q0018012Q00064Q0018012Q00044Q0018012Q00033Q0010560005001100090006D40009000B000100042Q0018012Q00034Q0018012Q00044Q0018012Q00014Q0018012Q00083Q0010560005001200090006D40009000C000100012Q0018012Q00033Q0010560005001300090006D40009000D000100012Q0018012Q00033Q0010560005001400090006D40009000E000100022Q0018012Q00034Q0018012Q00043Q0010560005001500090006D40009000F000100022Q0018012Q00044Q0018012Q00033Q001056000500160009000290010900103Q001056000500170009000290010900113Q001056000500180009000290010900123Q001056000500190009000290010900133Q0010560005001A00092Q00AA010500024Q0024012Q00013Q00143Q00073Q00030C3Q007365746D6574617461626C6503063Q004175726F726103063Q00466F6C64657203063Q006175726F726103063Q0049676E6F726503083Q004175746F6C6F616400010B3Q0012202Q0100014Q002A01026Q007000036Q008C2Q0100030002001056000100023Q0030050001000300042Q002A01025Q0010560001000500020030050001000600072Q00AA2Q0100024Q0024012Q00017Q00023Q0003063Q00466F6C64657203063Q006175726F726102063Q00060B010200030001000100049F012Q00030001001291000200023Q0010563Q000100022Q00AA012Q00024Q0024012Q00017Q00033Q0003063Q0049676E6F726503063Q006970616972732Q01020E4Q002A01025Q0010563Q00010002001220010200023Q00060B010300060001000100049F012Q000600012Q002A01036Q005E00020002000400049F012Q000A000100201001073Q00010020F9000700060003000677000200080001000200049F012Q000800012Q00AA012Q00024Q0024012Q00017Q00023Q0003063Q0049676E6F72652Q0102043Q00201001023Q00010020F90002000100022Q00AA012Q00024Q0024012Q00017Q00033Q0003063Q00466F6C64657203093Q002F636F6E666967732F03073Q00506C616365496401083Q0020102Q013Q0001001291000200024Q007000035Q0020100103000300032Q00F20003000100022Q006B2Q01000100032Q00AA2Q0100024Q0024012Q00017Q00033Q00030C3Q00436F6E666967466F6C64657203013Q002F03053Q002E6A736F6E02083Q0020E000023Q00014Q00020002000200122Q000300026Q000400013Q00122Q000500036Q0002000200054Q000200028Q00017Q00023Q0003063Q00466F6C646572030E3Q002F73652Q74696E67732E6A736F6E01053Q0020102Q013Q0001001291000200024Q006B2Q01000100022Q00AA2Q0100024Q0024012Q00017Q00243Q0003043Q005479706503063Q00546F2Q676C6503013Q007403043Q00622Q6F6C03013Q007603053Q0056616C75652Q0103063Q00536C6964657203063Q006E756D62657203053Q00496E70757403063Q00737472696E6703083Q00746F737472696E67034Q0003083Q0044726F70646F776E03053Q004D756C746903053Q007061697273026Q00F03F03053Q007461626C6503043Q00736F727403053Q006D756C746903063Q0073696E676C6503093Q004B65795069636B65722Q033Q006B657903073Q004B65794E616D6503043Q006D6F646503043Q004D6F6465030B3Q00436F6C6F725069636B657203053Q00636F6C6F7203013Q00682Q033Q0048756503013Q00732Q033Q0053617403013Q00622Q033Q0056616C03013Q006103053Q00416C706861015C3Q0020102Q013Q00010026470001000D0001000200049F012Q000D00012Q002A01023Q000200300500020003000400201001033Q0006002696000300090001000700049F012Q000900012Q001200036Q0065010300013Q0010560002000500032Q00AA010200023Q00049F012Q00590001002647000100150001000800049F012Q001500012Q002A01023Q000200306400020003000900202Q00033Q000600102Q0002000500034Q000200023Q00044Q00590001002647000100220001000A00049F012Q002200012Q002A01023Q000200300500020003000B0012200103000C3Q00201001043Q00060006FC0004001E0001000100049F012Q001E00010012910004000D4Q00890003000200020010560002000500032Q00AA010200023Q00049F012Q00590001002647000100410001000E00049F012Q0041000100201001023Q000F0006930002003B00013Q00049F012Q003B00012Q002A01025Q001220010300103Q00201001043Q00062Q005E00030002000500049F012Q003100010006930007003100013Q00049F012Q003100012Q0001000800023Q0020600008000800112Q004A0102000800060006770003002C0001000200049F012Q002C0001001220010300123Q0020100103000300132Q0018010400024Q00040103000200012Q002A01033Q00020030050003000300140010560003000500022Q00AA010300024Q002A01023Q000200306400020003001500202Q00033Q000600102Q0002000500034Q000200023Q00044Q005900010026470001004C0001001600049F012Q004C00012Q002A01023Q000300300500020003001700201100033Q00182Q008900030002000200105600020005000300201001033Q001A0010560002001900032Q00AA010200023Q00049F012Q00590001002647000100590001001B00049F012Q005900012Q002A01023Q000500300500020003001C00201001033Q001E0010230102001D000300202Q00033Q002000102Q0002001F000300202Q00033Q002200102Q00020021000300201001033Q00240010560002002300032Q00AA010200024Q001E000200024Q00AA010200024Q0024012Q00017Q00223Q0003043Q007479706503053Q007461626C6503043Q005479706503063Q00546F2Q676C6503013Q007403043Q00622Q6F6C03083Q0053657456616C756503013Q00762Q0103063Q00536C6964657203063Q006E756D62657203083Q00746F6E756D626572028Q0003053Q00496E70757403063Q00737472696E6703083Q0044726F70646F776E03053Q006D756C746903063Q0073696E676C6503093Q004B65795069636B65722Q033Q006B657903043Q006D6F646503073Q005365744D6F646503043Q006E6F6E65030B3Q00436F6C6F725069636B657203053Q00636F6C6F722Q033Q0048756503013Q00682Q033Q0053617403013Q00732Q033Q0056616C03013Q006203013Q006103053Q00416C70686103063Q005F7061696E7402873Q001220010200014Q0018010300014Q0089000200020002002696000200070001000200049F012Q000700012Q006501026Q00AA010200023Q00201001023Q0003002647000200180001000400049F012Q00180001002010010300010005002647000300180001000600049F012Q0018000100201100033Q0007002010010500010008002696000500120001000900049F012Q001200012Q001200056Q0065010500014Q0065010600014Q004D0103000600012Q0065010300014Q00AA010300023Q00049F012Q00840001002647000200290001000A00049F012Q00290001002010010300010005002647000300290001000B00049F012Q0029000100201100033Q00070012200105000C3Q0020100106000100082Q00890005000200020006FC000500240001000100049F012Q002400010012910005000D4Q0065010600014Q004D0103000600012Q0065010300014Q00AA010300023Q00049F012Q00840001002647000200350001000E00049F012Q00350001002010010300010005002647000300350001000F00049F012Q0035000100201100033Q00070020D80005000100084Q000600016Q0003000600014Q000300016Q000300023Q00044Q008400010026470002004E0001001000049F012Q004E0001002010010300010005002647000300440001001100049F012Q0044000100201100033Q00070020100105000100080006FC0005003F0001000100049F012Q003F00012Q002A01056Q0065010600014Q004D0103000600012Q0065010300014Q00AA010300023Q00049F012Q00840001002010010300010005002647000300840001001200049F012Q0084000100201100033Q00070020D80005000100084Q000600016Q0003000600014Q000300016Q000300023Q00044Q00840001002647000200640001001300049F012Q00640001002010010300010005002647000300640001001400049F012Q006400010020100103000100150006930003005A00013Q00049F012Q005A000100201100033Q00160020100105000100152Q0065010600014Q004D01030006000100201100033Q00070020100105000100080026470005005E0001001700049F012Q005E00010020100105000100082Q0065010600014Q004D0103000600012Q0065010300014Q00AA010300023Q00049F012Q00840001002647000200840001001800049F012Q00840001002010010300010005002647000300840001001900049F012Q0084000100201001030001001B0006FC0003006D0001000100049F012Q006D00010012910003000D3Q0010563Q001A000300201001030001001D0006FC000300720001000100049F012Q007200010012910003000D3Q0010563Q001C000300201001030001001F0006FC000300770001000100049F012Q007700010012910003000D3Q0010563Q001E00030020100103000100200006930003007D00013Q00049F012Q007D00010020100103000100200010563Q0021000300201001033Q00220006930003008200013Q00049F012Q0082000100201001033Q00222Q005E0103000100012Q0065010300014Q00AA010300024Q006501036Q00AA010300024Q0024012Q00017Q00013Q0003043Q0045616368010A4Q002A2Q016Q007000025Q0020100102000200010006D400033Q000100032Q0018017Q00703Q00014Q0018012Q00014Q00040102000200012Q00AA2Q0100024Q0024012Q00013Q00013Q00013Q0003063Q0049676E6F7265020E4Q007000025Q0020100102000200012Q0016010200023Q0006930002000600013Q00049F012Q000600012Q0024012Q00014Q0070000200014Q0018010300014Q00890002000200020006930002000D00013Q00049F012Q000D00012Q0070000300024Q004A01033Q00022Q0024012Q00017Q000D3Q00034Q0003143Q006E6F20636F6E666967206E616D6520676976656E03073Q0076657273696F6E03053Q00666C61677303073Q00436F2Q6C65637403053Q007063612Q6C03173Q00636F756C64206E6F7420656E636F646520636F6E66696703073Q0053746F7261676503073Q004D616B65446972030C3Q00436F6E666967466F6C64657203053Q00577269746503073Q0050617468466F7203183Q00636F756C64206E6F74207772697465207468652066696C65022D3Q0006930001000400013Q00049F012Q00040001002647000100070001000100049F012Q000700012Q006501025Q001291000300024Q00B6000200034Q002A01023Q00022Q005201035Q00102Q00020003000300202Q00033Q00054Q00030002000200102Q00020004000300122Q000300063Q0006D400043Q000100022Q00703Q00014Q0018012Q00024Q005E0003000200040006FC000300170001000100049F012Q001700012Q006501055Q001291000600074Q00B6000500034Q0070000500023Q00201001050005000800201001050005000900201100063Q000A2Q00F6000600074Q006101053Q00012Q0070000500023Q00201001050005000800201001050005000B00201100063Q000C2Q0018010800014Q008C0106000800022Q0018010700044Q008C0105000700020006FC0005002A0001000100049F012Q002A00012Q006501065Q0012910007000D4Q00B6000600034Q0065010600014Q00AA010600024Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E456E636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00103Q00034Q0003143Q006E6F20636F6E666967206E616D6520676976656E03073Q0053746F7261676503043Q005265616403073Q0050617468466F7203103Q00636F6E666967206E6F7420666F756E6403053Q007063612Q6C03043Q007479706503053Q007461626C6503183Q00636F6E6669672066696C65206973206D616C666F726D656403053Q00666C616773028Q0003053Q0070616972732Q033Q0047657403063Q0049676E6F7265026Q00F03F02483Q0006930001000400013Q00049F012Q00040001002647000100070001000100049F012Q000700012Q006501025Q001291000300024Q00B6000200034Q007000025Q00204E01020002000300202Q00020002000400202Q00033Q00054Q000500016Q000300056Q00023Q000200062Q000200130001000100049F012Q001300012Q006501035Q001291000400064Q00B6000300033Q001220010300073Q0006D400043Q000100022Q00703Q00014Q0018012Q00024Q005E0003000200040006930003001F00013Q00049F012Q001F0001001220010500084Q0018010600044Q0089000500020002002696000500220001000900049F012Q002200012Q006501055Q0012910006000A4Q00B6000500033Q00201001050004000B0006FC000500260001000100049F012Q002600012Q0018010500043Q0012910006000C3Q0012BC0007000C3Q00122Q0008000D6Q000900056Q00080002000A00044Q004100012Q0070000D00023Q002010010D000D000E2Q0018010E000B4Q0089000D00020002000693000D004000013Q00049F012Q00400001002010010E3Q000F2Q0016010E000E000B0006FC000E00400001000100049F012Q004000012Q0070000E00034Q0018010F000D4Q00180110000C4Q008C010E00100002000693000E003E00013Q00049F012Q003E000100206000060006001000049F012Q0041000100206000070007001000049F012Q004100010020600007000700100006770008002C0001000200049F012Q002C00012Q0065010800014Q0018010900064Q0018010A00074Q0026000800024Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E4465636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00073Q00034Q0003143Q006E6F20636F6E666967206E616D6520676976656E03073Q0053746F7261676503063Q0045786973747303073Q0050617468466F7203103Q00636F6E666967206E6F7420666F756E6403063Q0044656C657465021D3Q0006930001000400013Q00049F012Q00040001002647000100070001000100049F012Q000700012Q006501025Q001291000300024Q00B6000200034Q007000025Q00204E01020002000300202Q00020002000400202Q00033Q00054Q000500016Q000300056Q00023Q000200062Q000200130001000100049F012Q001300012Q006501025Q001291000300064Q00B6000200034Q007000025Q00201001020002000300201001020002000700201100033Q00052Q0018010500014Q0072010300054Q007301023Q00022Q001E000300034Q00B6000200034Q0024012Q00017Q000B3Q0003063Q0069706169727303073Q0053746F7261676503043Q004C697374030C3Q00436F6E666967466F6C6465722Q033Q00737562026Q0014C003053Q002E6A736F6E026Q00F03F03063Q005374656D4F6603053Q007461626C6503043Q00736F7274011F4Q002A2Q015Q001220010200014Q007000035Q00201001030003000200201001030003000300201100043Q00042Q00F6000400054Q007400036Q00A401023Q000400049F012Q00170001002011000700060005001291000900064Q008C010700090002002647000700170001000700049F012Q001700012Q0001000700013Q0020600007000700082Q007000085Q0020100108000800020020100108000800092Q0018010900064Q00890008000200022Q004A2Q01000700080006770002000A0001000200049F012Q000A00010012200102000A3Q00204000020002000B4Q000300016Q0002000200014Q000100028Q00017Q00063Q0003073Q0053746F7261676503043Q0052656164030C3Q0053652Q74696E67735061746803053Q007063612Q6C03043Q007479706503053Q007461626C65011B4Q00AE2Q015Q00202Q00010001000100202Q00010001000200202Q00023Q00034Q000200036Q00013Q000200062Q0001000A0001000100049F012Q000A00012Q002A01026Q00AA010200023Q001220010200043Q0006D400033Q000100022Q00703Q00014Q0018012Q00014Q005E0002000200030006930002001800013Q00049F012Q00180001001220010400054Q0018010500034Q0089000400020002002647000400180001000600049F012Q0018000100060B010400190001000300049F012Q001900012Q002A01046Q00AA010400024Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E4465636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00063Q0003083Q0053652Q74696E677303053Q00706169727303053Q007063612Q6C03073Q0053746F7261676503053Q005772697465030C3Q0053652Q74696E67735061746802193Q00201100023Q00012Q0089000200020002001220010300024Q0018010400014Q005E00030002000500049F012Q000700012Q004A010200060007000677000300060001000200049F012Q00060001001220010300033Q0006D400043Q000100022Q00708Q0018012Q00024Q005E0003000200040006930003001700013Q00049F012Q001700012Q0070000500013Q00201001050005000400201001050005000500201100063Q00062Q00890006000200022Q0018010700044Q004D0105000700012Q00AA010200024Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E456E636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00033Q0003083Q004175746F6C6F6164030D3Q00577269746553652Q74696E677303083Q006175746F6C6F616402073Q0010563Q0001000100201100023Q00022Q002A01043Q00010010560004000300012Q004D0102000400012Q00AA012Q00024Q0024012Q00017Q00023Q0003083Q0053652Q74696E677303083Q006175746F6C6F616401053Q00201100013Q00012Q00890001000200020020102Q01000100022Q00AA2Q0100024Q0024012Q00017Q00043Q00030B3Q004765744175746F6C6F6164034Q00030F3Q006E6F206175746F6C6F61642073657403043Q004C6F6164010E3Q00201100013Q00012Q00890001000200020006930001000600013Q00049F012Q00060001002647000100090001000200049F012Q000900012Q006501025Q001291000300034Q00B6000200033Q00201100023Q00042Q0018010400014Q0056010200044Q003500026Q0024012Q00017Q00253Q0003063Q004175726F7261030B3Q00412Q6447726F7570626F7803013Q0061030D3Q00636F6E66696775726174696F6E03083Q00412Q64496E70757403103Q00536176654D616E616765725F4E616D6503043Q005465787403043Q006E616D65030B3Q00506C616365686F6C64657203093Q006D792D636F6E666967030B3Q00412Q6444726F70646F776E03103Q00536176654D616E616765725F4C69737403063Q00636F6E66696703063Q0056616C75657303043Q004C69737403093Q00412Q6C6F774E752Q6C2Q0103083Q00412Q644C6162656C03153Q0063752Q72656E74206175746F6C6F61643A203C623E030B3Q004765744175746F6C6F616403043Q006E6F6E6503043Q003C2F623E03103Q0053657449676E6F7265496E6465786573030C3Q00412Q6442752Q746F6E526F7703063Q0063726561746503073Q0056617269616E7403073Q005072696D61727903083Q0043612Q6C6261636B03043Q006C6F616403043Q007361766503073Q007265667265736803083Q006175746F6C6F616403063Q0064656C65746503063Q0044616E67657203073Q00436F6E6669726D03093Q00436F6E666967426F78030B3Q00526566726573684C697374036C3Q00201001033Q000100201100040001000200060B010600050001000200049F012Q00050001001291000600033Q001291000700044Q008C010400070002002011000500040005001291000700064Q002A01083Q000200300500080007000800300500080009000A2Q008C01050008000200201100060004000B0012910008000C4Q002A01093Q000300300500090007000D002011000A3Q000F2Q0089000A000200020010560009000E000A0030050009001000112Q008C0106000900020020110007000400122Q002A01093Q0001001291000A00133Q002011000B3Q00142Q0089000B000200020006FC000B001E0001000100049F012Q001E0001001291000B00153Q001291000C00164Q00AC010A000A000C00102Q00090007000A4Q00070009000200202Q00083Q00174Q000A00023Q00122Q000B00063Q00122Q000C000C6Q000A000200012Q004D0108000A00010006D400083Q000100022Q0018012Q00064Q0018016Q0006D400090001000100012Q0018012Q00033Q002011000A000400182Q002A010C00034Q002A010D3Q0003003005000D00070019003005000D001A001B0006D4000E0002000100052Q0018012Q00054Q0018012Q00094Q0018017Q0018012Q00084Q0018012Q00063Q001056000D001C000E2Q002A010E3Q0002003005000E0007001D0006D4000F0003000100032Q0018012Q00064Q0018012Q00094Q0018016Q001056000E001C000F2Q002A010F3Q0002003005000F0007001E0006D400100004000100052Q0018012Q00064Q0018012Q00054Q0018012Q00094Q0018017Q0018012Q00083Q001056000F001C00102Q0025000C000300012Q004D010A000C0001002011000A000400182Q002A010C00034Q002A010D3Q0002003005000D0007001F0006D4000E0005000100032Q0018012Q00084Q0018012Q00094Q0018016Q001056000D001C000E2Q002A010E3Q0002003005000E000700200006D4000F0006000100042Q0018012Q00064Q0018012Q00094Q0018017Q0018012Q00073Q001056000E001C000F2Q002A010F3Q0004003005000F00070021003005000F001A0022003005000F002300110006D400100007000100042Q0018012Q00064Q0018017Q0018012Q00084Q0018012Q00093Q001056000F001C00102Q0025000C000300012Q004D010A000C00010010563Q002400040010563Q002500082Q00AA010400024Q0024012Q00013Q00083Q00023Q0003093Q0053657456616C75657303043Q004C69737400074Q0006016Q00206Q00014Q000200013Q00202Q0002000200024Q000200039Q0000016Q00017Q00043Q0003063Q004E6F7469667903053Q005469746C6503043Q005465787403073Q0056617269616E74030F4Q007000035Q0006930003000E00013Q00049F012Q000E00012Q007000035Q0020100103000300010006930003000E00013Q00049F012Q000E00012Q007000035Q00205B0003000300014Q00053Q000300102Q000500023Q00102Q00050003000100102Q0005000400024Q0003000500012Q0024012Q00017Q000D3Q0003053Q0056616C7565034Q0003073Q006E6F206E616D6503193Q0074797065206120636F6E666967206E616D652066697273742E03043Q005761726E03043Q005361766503083Q0053657456616C756503073Q006372656174656403073Q002073617665642E03073Q0053752Q63652Q7303063Q006661696C656403083Q00746F737472696E6703053Q00452Q726F7200264Q00707Q002010014Q00010026473Q000A0001000200049F012Q000A00012Q0070000100013Q00124F010200033Q00122Q000300043Q00122Q000400056Q0001000400016Q00014Q0070000100023Q0020110001000100062Q001801036Q00270001000300020006930001001E00013Q00049F012Q001E00012Q0070000300034Q005E0103000100012Q0070000300043Q0020110003000300072Q001801056Q004D0103000500012Q0070000300013Q001291000400084Q001801055Q001291000600094Q006B0105000500060012910006000A4Q004D01030006000100049F012Q002500012Q0070000300013Q0012910004000B3Q0012200105000C4Q0018010600024Q00890005000200020012910006000D4Q004D0103000600012Q0024012Q00017Q000F3Q0003053Q0056616C756503093Q006E6F20636F6E66696703143Q007069636B206120636F6E6669672066697273742E03043Q005761726E03043Q004C6F616403063Q006C6F61646564030A3Q0020726573746F7265642003083Q002076616C7565732E03073Q0053752Q63652Q73028Q0003073Q00736B692Q70656403183Q0020756E6B6E6F776E2076616C7565732069676E6F7265642E03063Q006661696C656403083Q00746F737472696E6703053Q00452Q726F72002D4Q00707Q002010014Q00010006FC3Q000A0001000100049F012Q000A00012Q0070000100013Q00124F010200023Q00122Q000300033Q00122Q000400046Q0001000400016Q00014Q0070000100023Q0020110001000100052Q001801036Q00270001000300030006930001002500013Q00049F012Q002500012Q0070000400013Q001291000500064Q001801065Q001291000700074Q0018010800023Q001291000900084Q006B010600060009001291000700094Q004D0104000700010006930003002C00013Q00049F012Q002C0001000EC8000A002C0001000300049F012Q002C00012Q0070000400013Q0012910005000B4Q0018010600033Q0012910007000C4Q006B010600060007001291000700044Q004D01040007000100049F012Q002C00012Q0070000400013Q0012910005000D3Q0012200106000E4Q0018010700024Q00890006000200020012910007000F4Q004D0104000700012Q0024012Q00017Q000C3Q0003053Q0056616C7565034Q0003093Q006E6F20636F6E666967031C3Q007069636B206F72206E616D65206120636F6E6669672066697273742E03043Q005761726E03043Q005361766503053Q00736176656403093Q00207772692Q74656E2E03073Q0053752Q63652Q7303063Q006661696C656403083Q00746F737472696E6703053Q00452Q726F7200284Q00707Q002010014Q00010006FC3Q00060001000100049F012Q000600012Q00703Q00013Q002010014Q00010006933Q000A00013Q00049F012Q000A00010026473Q00100001000200049F012Q001000012Q0070000100023Q00124F010200033Q00122Q000300043Q00122Q000400056Q0001000400016Q00014Q0070000100033Q0020110001000100062Q001801036Q00270001000300020006930001002000013Q00049F012Q002000012Q0070000300044Q005E0103000100012Q0070000300023Q001291000400074Q001801055Q001291000600084Q006B010500050006001291000600094Q004D01030006000100049F012Q002700012Q0070000300023Q0012910004000A3Q0012200105000B4Q0018010600024Q00890005000200020012910006000C4Q004D0103000600012Q0024012Q00017Q00033Q0003093Q0072656672657368656403043Q004C697374030F3Q0020636F6E6669677320666F756E642E000C4Q00708Q005E012Q000100012Q00703Q00013Q001291000100014Q0070000200023Q0020110002000200022Q00890002000200022Q0001000200023Q001291000300034Q006B0102000200032Q004D012Q000200012Q0024012Q00017Q000B3Q0003053Q0056616C756503093Q006E6F20636F6E66696703143Q007069636B206120636F6E6669672066697273742E03043Q005761726E030B3Q005365744175746F6C6F616403073Q005365745465787403153Q0063752Q72656E74206175746F6C6F61643A203C623E03043Q003C2F623E030C3Q006175746F6C6F61642073657403113Q00206C6F616473206F6E20696E6A6563742E03073Q0053752Q63652Q73001D4Q00707Q002010014Q00010006FC3Q000A0001000100049F012Q000A00012Q0070000100013Q00124F010200023Q00122Q000300033Q00122Q000400046Q0001000400016Q00014Q0070000100023Q00207F0001000100054Q00038Q0001000300014Q000100033Q00202Q00010001000600122Q000300076Q00045Q00122Q000500086Q0003000300054Q0001000300012Q0070000100013Q001291000200094Q001801035Q0012910004000A4Q006B0103000300040012910004000B4Q004D2Q01000400012Q0024012Q00017Q00063Q0003053Q0056616C756503063Q0044656C65746503083Q0053657456616C756503073Q0064656C6574656403093Q002072656D6F7665642E03053Q00452Q726F7200174Q00707Q002010014Q00010006FC3Q00050001000100049F012Q000500012Q0024012Q00014Q0070000100013Q0020F40001000100024Q00038Q0001000300014Q000100026Q0001000100014Q00015Q00202Q0001000100034Q000300036Q0001000300014Q000100033Q00122Q000200046Q00035Q00122Q000400056Q00030003000400122Q000400066Q0001000400016Q00017Q002C3Q00030A3Q00636F72652F5468656D6503093Q00636F72652F5574696C030D3Q00636F72652F506C6174666F726D03043Q0067616D65030A3Q0047657453657276696365030B3Q00482Q74705365727669636503073Q002Q5F696E64657803073Q005072657365747303043Q0070696E6B03063Q00612Q63656E7403063Q004546434644392Q033Q0077696E03063Q0031383138314203023Q00686903063Q0044364436444103043Q006D696E7403063Q0038464533424503063Q0031343138314103063Q0044344443443803053Q00616D62657203063Q0045334234373803063Q0031413138313403063Q00444344362Q432Q033Q0069636503063Q0042464434454303063Q0031343136314303063Q004432443845322Q033Q0061736803063Q0044384438444303063Q00313731373139030B3Q005072657365744F726465722Q033Q006E657703093Q00536574466F6C646572030B3Q005468656D65466F6C64657203073Q0050617468466F72030C3Q0053652Q74696E677350617468030A3Q00412Q706C795468656D6503083Q00536E617073686F7403093Q00536176655468656D65030B3Q0044656C6574655468656D6503043Q004C697374030A3Q0053657444656661756C74030B3Q004C6F616444656661756C7403113Q004275696C645468656D6553656374696F6E01624Q009900015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q00030002000200122Q000400043Q002011000400040005001291000600064Q008C0104000600022Q002A01055Q0010560005000700052Q002A01063Q00052Q002A01073Q00030030050007000A000B0030050007000C000D0030050007000E000F0010560006000900072Q002A01073Q00030030050007000A00110030050007000C00120030050007000E00130010560006001000072Q002A01073Q00030030050007000A00150030050007000C00160030050007000E00170010560006001400072Q002A01073Q00030030050007000A00190030050007000C001A0030050007000E001B0010560006001800072Q002A01073Q00030030050007000A001D0030050007000C001E0030050007000E001D0010560006001C00070010560005000800062Q002A010600053Q001291000700093Q001291000800103Q001291000900143Q001291000A00183Q001291000B001C4Q00250006000500010010560005001F00060006D400063Q000100012Q0018012Q00053Q001056000500200006000290010600013Q001056000500210006000290010600023Q001056000500220006000290010600033Q001056000500230006000290010600043Q0010560005002400060006D400060005000100052Q0018012Q00054Q0018012Q00034Q0018012Q00044Q0018012Q00014Q0018012Q00023Q0010560005002500060006D400060006000100022Q0018012Q00024Q0018012Q00013Q0010560005002600060006D400060007000100022Q0018012Q00044Q0018012Q00033Q0010560005002700060006D400060008000100022Q0018012Q00054Q0018012Q00033Q0010560005002800060006D400060009000100022Q0018012Q00054Q0018012Q00033Q0010560005002900060006D40006000A000100022Q0018012Q00034Q0018012Q00043Q0010560005002A00060006D40006000B000100022Q0018012Q00034Q0018012Q00043Q0010560005002B00060006D40006000C000100022Q0018012Q00024Q0018012Q00013Q0010560005002C00062Q00AA010500024Q0024012Q00013Q000D3Q00063Q00030C3Q007365746D6574617461626C6503063Q004175726F726103063Q00466F6C64657203063Q006175726F726103073Q0043752Q72656E7403043Q0070696E6B01093Q00127A000100016Q00028Q00038Q00010003000200102Q000100023Q00302Q00010003000400302Q0001000500064Q000100028Q00017Q00023Q0003063Q00466F6C64657203063Q006175726F726102063Q00060B010200030001000100049F012Q00030001001291000200023Q0010563Q000100022Q00AA012Q00024Q0024012Q00017Q00023Q0003063Q00466F6C64657203073Q002F7468656D657301053Q0020102Q013Q0001001291000200024Q006B2Q01000100022Q00AA2Q0100024Q0024012Q00017Q00033Q00030B3Q005468656D65466F6C64657203013Q002F03053Q002E6A736F6E02083Q0020E000023Q00014Q00020002000200122Q000300026Q000400013Q00122Q000500036Q0002000200054Q000200028Q00017Q00023Q0003063Q00466F6C646572030E3Q002F73652Q74696E67732E6A736F6E01053Q0020102Q013Q0001001291000200024Q006B2Q01000100022Q00AA2Q0100024Q0024012Q00017Q00223Q0003043Q007479706503063Q00737472696E6703073Q005072657365747303073Q0053746F7261676503043Q005265616403073Q0050617468466F7203053Q007063612Q6C03053Q007461626C65030D3Q006E6F2073756368207468656D6503073Q0043752Q72656E7403063Q00612Q63656E7403093Q00536574412Q63656E74030A3Q00686578546F436F6C6F722Q033Q0077696E03083Q00536574546F6B656E03093Q00636F6C6F722E77696E030A3Q00636F6C6F722E6D61736B03063Q00436F6C6F72332Q033Q006E657703043Q006D6174682Q033Q006D696E026Q00F03F03013Q0052021F85EB51B81EF13F03013Q004703013Q0042030E3Q00636F6C6F722E656C657661746564026Q33F33F03023Q00686903083Q00636F6C6F722E68692Q033Q006D696403093Q00636F6C6F722E6D696403023Q006C6F03083Q00636F6C6F722E6C6F029B4Q0018010200013Q001220010300014Q0018010400014Q00890003000200020026470003002A0001000200049F012Q002A00012Q007000035Q0020100103000300032Q00160102000300010006FC000200240001000100049F012Q002400012Q0070000300013Q00201001030003000400201001030003000500201100043Q00062Q0018010600014Q0072010400064Q007301033Q00020006930003002300013Q00049F012Q00230001001220010400073Q0006D400053Q000100022Q00703Q00024Q0018012Q00034Q005E0004000200050006930004002200013Q00049F012Q00220001001220010600014Q0018010700054Q0089000600020002002647000600220001000800049F012Q0022000100060B010200230001000500049F012Q002300012Q001E000200024Q00A801035Q0006FC000200290001000100049F012Q002900012Q006501035Q001291000400094Q00B6000300033Q0010563Q000A000100201001030002000B0006930003003700013Q00049F012Q003700012Q0070000300033Q00201001030003000C2Q0070000400043Q00201001040004000D00201001050002000B2Q00890004000200020006FC000400360001000100049F012Q0036000100201001040002000B2Q000401030002000100201001030002000E0006930003007700013Q00049F012Q007700012Q0070000300043Q00201001030003000D00201001040002000E2Q00890003000200020006930003007700013Q00049F012Q007700012Q0070000400033Q00200001040004000F00122Q000500106Q000600036Q0004000600014Q000400033Q00202Q00040004000F00122Q000500113Q00122Q000600123Q00202Q00060006001300122Q000700143Q002010010700070015001291000800163Q00201001090003001700201F0109000900182Q008C010700090002001220010800143Q002010010800080015001291000900163Q002010010A000300190020CD000A000A00184Q0008000A000200122Q000900143Q00202Q00090009001500122Q000A00163Q00202Q000B0003001A00202Q000B000B00184Q0009000B6Q00068Q00043Q00012Q0070000400033Q00201001040004000F0012910005001B3Q001239000600123Q00202Q00060006001300122Q000700143Q00202Q00070007001500122Q000800163Q00202Q00090003001700202Q00090009001C4Q00070009000200122Q000800143Q00202Q000800080015001291000900163Q002010010A000300190020CD000A000A001C4Q0008000A000200122Q000900143Q00202Q00090009001500122Q000A00163Q00202Q000B0003001A00202Q000B000B001C4Q0009000B6Q00068Q00043Q000100201001030002001D0006930003008200013Q00049F012Q008200012Q0070000300033Q00201001030003000F0012910004001E4Q0070000500043Q00201001050005000D00201001060002001D2Q00F6000500064Q006101033Q000100201001030002001F0006930003008D00013Q00049F012Q008D00012Q0070000300033Q00201001030003000F001291000400204Q0070000500043Q00201001050005000D00201001060002001F2Q00F6000500064Q006101033Q00010020100103000200210006930003009800013Q00049F012Q009800012Q0070000300033Q00201001030003000F001291000400224Q0070000500043Q00201001050005000D0020100106000200212Q00F6000500064Q006101033Q00012Q0065010300014Q00AA010300024Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E4465636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q000C3Q0003063Q00612Q63656E74030A3Q00636F6C6F72546F4865782Q033Q00476574030C3Q00636F6C6F722E612Q63656E742Q033Q0077696E03093Q00636F6C6F722E77696E03023Q00686903083Q00636F6C6F722E68692Q033Q006D696403093Q00636F6C6F722E6D696403023Q006C6F03083Q00636F6C6F722E6C6F012B4Q002A2Q013Q00052Q007000025Q0020100102000200022Q0025010300013Q00202Q00030003000300122Q000400046Q000300046Q00023Q000200102Q0001000100024Q00025Q00202Q0002000200024Q000300013Q00202Q000300030003001291000400064Q00AD000300046Q00023Q000200102Q0001000500024Q00025Q00202Q0002000200024Q000300013Q00202Q00030003000300122Q000400086Q000300046Q00023Q00020010560001000700022Q007000025Q0020100102000200022Q0025010300013Q00202Q00030003000300122Q0004000A6Q000300046Q00023Q000200102Q0001000900024Q00025Q00202Q0002000200024Q000300013Q00202Q0003000300030012910004000C4Q00F6000300044Q007301023Q00020010560001000B00022Q00AA2Q0100024Q0024012Q00017Q00093Q00034Q0003133Q006E6F207468656D65206E616D6520676976656E03053Q007063612Q6C03163Q00636F756C64206E6F7420656E636F6465207468656D6503073Q0053746F7261676503073Q004D616B65446972030B3Q005468656D65466F6C64657203053Q00577269746503073Q0050617468466F7202213Q0006930001000400013Q00049F012Q00040001002647000100070001000100049F012Q000700012Q006501025Q001291000300024Q00B6000200033Q001220010200033Q0006D400033Q000100022Q00708Q0018017Q005E0002000200030006FC000200110001000100049F012Q001100012Q006501045Q001291000500044Q00B6000400034Q0070000400013Q00201001040004000500201001040004000600201100053Q00072Q00F6000500064Q006101043Q00012Q0070000400013Q00201001040004000500201001040004000800201100053Q00092Q0018010700014Q008C0105000700022Q0018010600034Q0056010400064Q003500046Q0024012Q00013Q00013Q00023Q00030A3Q004A534F4E456E636F646503083Q00536E617073686F7400084Q00707Q0020115Q00012Q0070000200013Q0020110002000200022Q00F6000200034Q0092017Q00358Q0024012Q00017Q000A3Q0003073Q005072657365747303213Q006275696C742D696E207468656D65732063612Q6E6F742062652064656C6574656403073Q0053746F7261676503063Q0045786973747303073Q0050617468466F72030F3Q007468656D65206E6F7420666F756E6403063Q0044656C65746503073Q0043752Q72656E74030A3Q00412Q706C795468656D6503043Q0070696E6B02254Q007000025Q0020100102000200012Q00160102000200010006930002000800013Q00049F012Q000800012Q006501025Q001291000300024Q00B6000200034Q0070000200013Q00204E01020002000300202Q00020002000400202Q00033Q00054Q000500016Q000300056Q00023Q000200062Q000200140001000100049F012Q001400012Q006501025Q001291000300064Q00B6000200034Q0070000200013Q00201001020002000300201001020002000700201100033Q00052Q0018010500014Q0072010300054Q007301023Q00020006930002002300013Q00049F012Q0023000100201001033Q000800066A010300230001000100049F012Q0023000100201100033Q00090012910005000A4Q004D0103000500012Q00AA010200024Q0024012Q00017Q000B3Q0003063Q00697061697273030B3Q005072657365744F72646572026Q00F03F03073Q0053746F7261676503043Q004C697374030B3Q005468656D65466F6C6465722Q033Q00737562026Q0014C003053Q002E6A736F6E03063Q005374656D4F6603073Q0050726573657473012A4Q00602Q015Q00122Q000200016Q00035Q00202Q0003000300024Q00020002000400044Q000900012Q0001000700013Q0020600007000700032Q004A2Q0100070006000677000200060001000200049F012Q00060001001220010200014Q0070000300013Q00201001030003000400201001030003000500201100043Q00062Q00F6000400054Q007400036Q00A401023Q000400049F012Q00260001002011000700060007001291000900084Q008C010700090002002647000700260001000900049F012Q002600012Q0070000700013Q00201001070007000400201001070007000A2Q0018010800064Q00890007000200022Q007000085Q00201001080008000B2Q00160108000800070006FC000800260001000100049F012Q002600012Q0001000800013Q0020600008000800032Q004A2Q0100080007000677000200140001000200049F012Q001400012Q00AA2Q0100024Q0024012Q00017Q00083Q0003073Q0053746F7261676503043Q0052656164030C3Q0053652Q74696E67735061746803053Q007063612Q6C03043Q007479706503053Q007461626C6503053Q007468656D6503053Q00577269746502274Q007000025Q00201001020002000100201001020002000200201100033Q00032Q00F6000300044Q007301023Q00022Q002A01035Q0006930002001600013Q00049F012Q00160001001220010400043Q0006D400053Q000100022Q00703Q00014Q0018012Q00024Q005E0004000200050006930004001600013Q00049F012Q00160001001220010600054Q0018010700054Q0089000600020002002647000600160001000600049F012Q001600012Q0018010300053Q001056000300070001001220010400043Q0006D400050001000100022Q00703Q00014Q0018012Q00034Q005E0004000200050006930004002500013Q00049F012Q002500012Q007000065Q00201001060006000100201001060006000800201100073Q00032Q00890007000200022Q0018010800054Q004D0106000800012Q00AA012Q00024Q0024012Q00013Q00023Q00013Q00030A3Q004A534F4E4465636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00013Q00030A3Q004A534F4E456E636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q00083Q0003073Q0053746F7261676503043Q0052656164030C3Q0053652Q74696E67735061746803053Q007063612Q6C03043Q007479706503053Q007461626C6503053Q007468656D65030A3Q00412Q706C795468656D6501204Q00AE2Q015Q00202Q00010001000100202Q00010001000200202Q00023Q00034Q000200036Q00013Q000200062Q0001000A0001000100049F012Q000A00012Q006501026Q00AA010200023Q001220010200043Q0006D400033Q000100022Q00703Q00014Q0018012Q00014Q005E0002000200030006930002001900013Q00049F012Q00190001001220010400054Q0018010500034Q0089000400020002002647000400190001000600049F012Q001900010020100104000300070006FC0004001B0001000100049F012Q001B00012Q006501046Q00AA010400023Q00201100043Q00080020100106000300072Q0056010400064Q003500046Q0024012Q00013Q00013Q00013Q00030A3Q004A534F4E4465636F646500064Q001D016Q00206Q00014Q000200018Q00029Q008Q00017Q002A3Q0003063Q004175726F7261030B3Q00412Q6447726F7570626F7803013Q006203053Q007468656D65030B3Q00412Q6444726F70646F776E03133Q005468656D654D616E616765725F50726573657403043Q005465787403063Q0070726573657403063Q0056616C75657303043Q004C69737403073Q0044656661756C7403073Q0043752Q72656E7403083Q0043612Q6C6261636B030E3Q00412Q64436F6C6F725069636B657203133Q005468656D654D616E616765725F412Q63656E7403063Q00612Q63656E74030A3Q00636F6C6F72546F4865782Q033Q00476574030C3Q00636F6C6F722E612Q63656E7403173Q005468656D654D616E616765725F4261636B67726F756E64030A3Q006261636B67726F756E6403093Q00636F6C6F722E77696E03113Q005468656D654D616E616765725F5465787403043Q007465787403083Q00636F6C6F722E686903083Q00412Q64496E70757403113Q005468656D654D616E616765725F4E616D6503043Q006E616D65030B3Q00506C616365686F6C64657203083Q006D792D7468656D65030C3Q00412Q6442752Q746F6E526F7703043Q007361766503073Q0056617269616E7403073Q005072696D617279030B3Q007365742064656661756C7403053Q00726573657403063Q0044616E67657203073Q00436F6E6669726D2Q01030B3Q00536176654D616E61676572030B3Q0049676E6F7265496E64657803083Q005468656D65426F7803853Q00201001033Q000100201100040001000200060B010600050001000200049F012Q00050001001291000600033Q001291000700044Q006800040007000200202Q00050004000500122Q000700066Q00083Q000400302Q00080007000800202Q00093Q000A4Q00090002000200102Q00080009000900202Q00093Q000C00102Q0008000B00090006D400093Q000100012Q0018016Q0010560008000D00092Q008C01050008000200201100060004000E0012910008000F4Q002A01093Q00030030050009000700102Q0070000A5Q002010010A000A00112Q0070000B00013Q002010010B000B0012001291000C00134Q00F6000B000C4Q0073010A3Q00020010560009000B000A0006D4000A0001000100012Q00703Q00013Q0010560009000D000A2Q004D01060009000100201100060004000E001291000800144Q002A01093Q00030030050009000700152Q0070000A5Q002010010A000A00112Q0070000B00013Q002010010B000B0012001291000C00164Q00F6000B000C4Q0073010A3Q00020010560009000B000A0006D4000A0002000100012Q00703Q00013Q0010560009000D000A2Q004D01060009000100201100060004000E001291000800174Q002A01093Q00030030050009000700182Q0070000A5Q002010010A000A00112Q0070000B00013Q002010010B000B0012001291000C00194Q00F6000B000C4Q0073010A3Q00020010560009000B000A0006D4000A0003000100012Q00703Q00013Q0010560009000D000A2Q004D01060009000100201100060004001A0012910008001B4Q002A01093Q000200300500090007001C0030050009001D001E2Q008C0106000900020006D400070004000100012Q0018012Q00033Q00201100080004001F2Q002A010A00034Q002A010B3Q0003003005000B00070020003005000B002100220006D4000C0005000100042Q0018012Q00064Q0018012Q00074Q0018017Q0018012Q00053Q001056000B000D000C2Q002A010C3Q0002003005000C000700230006D4000D0006000100032Q0018012Q00054Q0018017Q0018012Q00073Q001056000C000D000D2Q002A010D3Q0004003005000D00070024003005000D00210025003005000D002600270006D4000E0007000100032Q00703Q00014Q0018017Q0018012Q00073Q001056000D000D000E2Q0025000A000300012Q004D0108000A00010006930003008200013Q00049F012Q008200010020100108000300280006930008008200013Q00049F012Q0082000100201001080003002800207100080008002900122Q000A00066Q0008000A000100202Q00080003002800202Q00080008002900122Q000A000F6Q0008000A000100202Q00080003002800202Q00080008002900122Q000A00146Q0008000A000100202Q00080003002800202Q00080008002900122Q000A00176Q0008000A000100202Q00080003002800202Q00080008002900122Q000A001B6Q0008000A00010010563Q002A00042Q00AA010400024Q0024012Q00013Q00083Q00013Q00030A3Q00412Q706C795468656D6501073Q0006933Q000600013Q00049F012Q000600012Q007000015Q0020110001000100012Q001801036Q004D2Q01000300012Q0024012Q00017Q00013Q0003093Q00536574412Q63656E7401054Q007000015Q0020102Q01000100012Q001801026Q00042Q01000200012Q0024012Q00017Q000E3Q0003083Q00536574546F6B656E03093Q00636F6C6F722E77696E030A3Q00636F6C6F722E6D61736B03063Q00436F6C6F72332Q033Q006E657703043Q006D6174682Q033Q006D696E026Q00F03F03013Q0052021F85EB51B81EF13F03013Q004703013Q0042030E3Q00636F6C6F722E656C657661746564026Q33F33F01384Q007000015Q0020002Q010001000100122Q000200026Q00038Q0001000300014Q00015Q00202Q00010001000100122Q000200033Q00122Q000300043Q00202Q00030003000500122Q000400063Q002010010400040007001291000500083Q00201001063Q000900201F01060006000A2Q008C010400060002001220010500063Q002010010500050007001291000600083Q00201001073Q000B0020CD00070007000A4Q00050007000200122Q000600063Q00202Q00060006000700122Q000700083Q00202Q00083Q000C00202Q00080008000A4Q000600086Q00038Q00013Q00012Q007000015Q0020102Q01000100010012910002000D3Q001239000300043Q00202Q00030003000500122Q000400063Q00202Q00040004000700122Q000500083Q00202Q00063Q000900202Q00060006000E4Q00040006000200122Q000500063Q00202Q000500050007001291000600083Q00201001073Q000B0020CD00070007000E4Q00050007000200122Q000600063Q00202Q00060006000700122Q000700083Q00202Q00083Q000C00202Q00080008000E4Q000600086Q00038Q00013Q00012Q0024012Q00017Q00023Q0003083Q00536574546F6B656E03083Q00636F6C6F722E686901064Q000E2Q015Q00202Q00010001000100122Q000200026Q00038Q0001000300016Q00017Q00043Q0003063Q004E6F7469667903053Q005469746C6503043Q005465787403073Q0056617269616E74030F4Q007000035Q0006930003000E00013Q00049F012Q000E00012Q007000035Q0020100103000300010006930003000E00013Q00049F012Q000E00012Q007000035Q00205B0003000300014Q00053Q000300102Q000500023Q00102Q00050003000100102Q0005000400024Q0003000500012Q0024012Q00017Q000E3Q0003053Q0056616C7565034Q0003073Q006E6F206E616D6503183Q00747970652061207468656D65206E616D652066697273742E03043Q005761726E03093Q00536176655468656D6503093Q0053657456616C75657303043Q004C69737403053Q00736176656403083Q002073746F7265642E03073Q0053752Q63652Q7303063Q006661696C6564031A3Q00636F756C64206E6F7420777269746520746865207468656D652E03053Q00452Q726F7200244Q00707Q002010014Q00010026473Q000A0001000200049F012Q000A00012Q0070000100013Q00124F010200033Q00122Q000300043Q00122Q000400056Q0001000400016Q00014Q0070000100023Q0020110001000100062Q001801036Q008C2Q01000300020006930001001E00013Q00049F012Q001E00012Q0070000100033Q0020110001000100072Q0070000300023Q0020110003000300082Q00F6000300044Q00612Q013Q00012Q0070000100013Q001291000200094Q001801035Q0012910004000A4Q006B0103000300040012910004000B4Q004D2Q010004000100049F012Q002300012Q0070000100013Q0012910002000C3Q0012910003000D3Q0012910004000E4Q004D2Q01000400012Q0024012Q00017Q00063Q0003053Q0056616C756503073Q0043752Q72656E74030A3Q0053657444656661756C74030B3Q0064656661756C742073657403113Q0020612Q706C696573206F6E206C6F61642E03073Q0053752Q63652Q7300124Q00707Q002010014Q00010006FC3Q00060001000100049F012Q000600012Q00703Q00013Q002010014Q00022Q0070000100013Q0020DC0001000100034Q00038Q0001000300014Q000100023Q00122Q000200046Q00035Q00122Q000400056Q00030003000400122Q000400066Q0001000400016Q00017Q00053Q0003053Q00526573657403073Q0043752Q72656E7403043Q0070696E6B03053Q007265736574031C3Q006261636B20746F20746865207368692Q7065642070616C652Q74652E000A4Q00707Q002010014Q00012Q005E012Q000100012Q00703Q00013Q0030053Q000200032Q00703Q00023Q001291000100043Q001291000200054Q004D012Q000200012Q0024012Q00017Q00123Q00030A3Q00636F72652F466C616773030A3Q00636F72652F5468656D65030B3Q00636F72652F4D6F74696F6E030B3Q00636F72652F486F746B657903093Q00636F72652F4D61696403093Q00636F72652F5574696C030D3Q00636F72652F506C6174666F726D03113Q00636F6D706F6E656E74732F57696E646F7703143Q00636F6D706F6E656E74732F4B65795069636B6572030E3Q006F7665726C6179732F4C6179657203153Q006F7665726C6179732F4E6F74696669636174696F6E030F3Q006F7665726C6179732F4469616C6F6703103Q006F7665726C6179732F542Q6F6C74697003123Q006F7665726C6179732F57617465726D61726B03143Q006F7665726C6179732F4B657962696E644C697374030F3Q006F7665726C6179732F53656172636803143Q006D616E61676572732F536176654D616E6167657203153Q006D616E61676572732F5468656D654D616E61676572014B4Q008200015Q00122Q000200016Q0001000200024Q00025Q00122Q000300026Q0002000200024Q00035Q00122Q000400036Q0003000200024Q00045Q001291000500044Q00890004000200022Q008200055Q00122Q000600056Q0005000200024Q00065Q00122Q000700066Q0006000200024Q00075Q00122Q000800076Q0007000200024Q00085Q001291000900084Q00890008000200022Q008200095Q00122Q000A00096Q0009000200024Q000A5Q00122Q000B000A6Q000A000200024Q000B5Q00122Q000C000B6Q000B000200024Q000C5Q001291000D000C4Q0089000C000200022Q0082000D5Q00122Q000E000D6Q000D000200024Q000E5Q00122Q000F000E6Q000E000200024Q000F5Q00122Q0010000F6Q000F000200024Q00105Q001291001100104Q00890010000200022Q001801115Q001291001200114Q00890011000200022Q001801125Q001291001300124Q00890012000200020006D400133Q000100122Q0018012Q00024Q0018012Q00034Q0018012Q00064Q0018012Q00074Q0018012Q00014Q0018012Q00054Q0018012Q00114Q0018012Q00124Q0018012Q00084Q0018012Q000B4Q0018012Q000C4Q0018012Q000D4Q0018012Q00104Q0018012Q000E4Q0018012Q000F4Q0018012Q000A4Q0018012Q00044Q0018012Q00094Q00AA011300024Q0024012Q00013Q00013Q00163Q0003073Q0056657273696F6E03053Q00312E302E3003053Q005468656D6503063Q004D6F74696F6E03043Q005574696C03083Q00506C6174666F726D03053Q00466C61677303073Q00546F2Q676C657303073Q004F7074696F6E7303073Q0057696E646F777303043Q004D6169642Q033Q006E657703083Q00556E6C6F616465640100030B3Q00536176654D616E61676572030C3Q005468656D654D616E61676572030C3Q0043726561746557696E646F7703063Q004E6F7469667903063Q004469616C6F6703093Q00536574412Q63656E7403113Q005365744D6F74696F6E4475726174696F6E03063Q00556E6C6F616400504Q0017016Q00304Q000100024Q00015Q00104Q000300014Q000100013Q00104Q000400014Q000100023Q00104Q000500014Q000100033Q00104Q000600012Q0070000100043Q0010563Q000700012Q0070000100043Q0020102Q01000100080010563Q000800012Q0070000100043Q0020102Q01000100090010563Q000900012Q002A2Q015Q0010563Q000A00012Q0070000100053Q0020102Q010001000C2Q00F20001000100020010563Q000B00010030053Q000D000E2Q0070000100063Q0020102Q010001000C2Q001801026Q00890001000200020010563Q000F00012Q0070000100073Q0020102Q010001000C2Q001801026Q00890001000200020010563Q001000010002902Q016Q0018010200013Q001291000300084Q0070000400043Q0020100104000400082Q004D0102000400012Q0018010200013Q001291000300094Q0070000400043Q0020100104000400092Q004D0102000400010006D400020001000100072Q00703Q00084Q00703Q00094Q00703Q000A4Q00703Q000B4Q00703Q000C4Q00703Q000D4Q00703Q000E3Q0010563Q001100020006D400020002000100012Q00703Q00093Q0010563Q001200020006D400020003000100012Q00703Q000A3Q0010563Q001300020006D400020004000100012Q00707Q0010563Q001400020006D400020005000100012Q00703Q00013Q0010563Q001500020006D400020006000100092Q00703Q000F4Q00703Q00094Q00703Q000A4Q00703Q000B4Q00703Q00104Q00703Q00114Q00703Q00044Q0018012Q00014Q00707Q0010563Q001600022Q00AA012Q00024Q0024012Q00013Q00073Q00013Q0003053Q007063612Q6C020B3Q001220010200013Q0006D400033Q000100022Q0018017Q0018012Q00014Q0004010200020001001220010200013Q0006D400030001000100022Q0018017Q0018012Q00014Q00040102000200012Q0024012Q00013Q00023Q00013Q0003073Q0067657467656E7600063Q001220012Q00014Q00F23Q000100022Q007000016Q0070000200014Q004A012Q000100022Q0024012Q00017Q00013Q0003023Q005F4700053Q001220012Q00014Q007000016Q0070000200014Q004A012Q000100022Q0024012Q00017Q00163Q002Q033Q006E657703073Q0057696E646F7773026Q00F03F03063Q0057696E646F7703043Q004D61696403043Q004769766503043Q00496E69742Q033Q0047756903063Q0053656172636803093Q0057617465726D61726B010003053Q005469746C6503063Q006175726F726103073Q0056697369626C652Q0100030B3Q004B657962696E644C697374030C3Q0053657457617465726D61726B030E3Q005365744B657962696E644C69737403053Q005468656D65030C3Q005468656D654D616E61676572030A3Q00412Q706C795468656D6502633Q0006FC000100040001000100049F012Q000400012Q002A01026Q00182Q0100024Q007000025Q00202B0002000200014Q00038Q000400016Q00020004000200202Q00033Q000200202Q00043Q00024Q000400043Q00202Q0004000400034Q00030004000200104Q0004000200203300033Q000500202Q0003000300064Q000500026Q0003000500014Q000300013Q0020100103000300070020100104000200082Q00040103000200012Q0070000300023Q0020100103000300070020100104000200082Q00040103000200012Q0070000300033Q0020100103000300070020100104000200082Q00040103000200012Q0070000300043Q0020100103000300012Q0018010400024Q008900030002000200105600020009000300201001033Q00050020110003000300060020100105000200092Q004D01030005000100201001030001000A002696000300430001000B00049F012Q004300012Q0070000300053Q0020100103000300010020100104000200082Q002A01053Q000200201001060001000C0006FC000600330001000100049F012Q003300010012910006000D3Q0010560005000C000600201001060001000A0026960006003B0001000F00049F012Q003B000100201001060001000A0026960006003B0001001000049F012Q003B00012Q001200066Q0065010600013Q0010560005000E00062Q008C0103000500020010560002000A000300201001033Q000500201100030003000600201001050002000A2Q004D010300050001002010010300010011002696000300560001000B00049F012Q005600012Q0070000300063Q00200201030003000100202Q0004000200084Q00053Q000100202Q00060001001100262Q0006004E0001000B00049F012Q004E00012Q001200066Q0065010600013Q0010560005000E00062Q008C01030005000200105600020011000300201001033Q00050020110003000300060020100105000200112Q004D01030005000100029001035Q001056000200120003000290010300013Q0010560002001300030020100103000100140006930003006100013Q00049F012Q0061000100201001033Q00150020110003000300160020100105000100142Q004D0103000500012Q00AA010200024Q0024012Q00013Q00023Q00023Q0003093Q0057617465726D61726B030A3Q0053657456697369626C6502093Q00201001023Q00010006930002000700013Q00049F012Q0007000100201001023Q00010020110002000200022Q0018010400014Q004D0102000400012Q00AA012Q00024Q0024012Q00017Q00023Q00030B3Q004B657962696E644C697374030A3Q0053657456697369626C6502093Q00201001023Q00010006930002000700013Q00049F012Q0007000100201001023Q00010020110002000200022Q0018010400014Q004D0102000400012Q00AA012Q00024Q0024012Q00017Q00043Q0003043Q007479706503063Q00737472696E6703043Q005465787403063Q004E6F74696679020E3Q001220010200014Q0018010300014Q0089000200020002002647000200080001000200049F012Q000800012Q002A01023Q00010010560002000300012Q00182Q0100024Q007000025Q0020B40002000200044Q000300016Q000200036Q00029Q0000017Q00013Q0003043Q0053686F7702064Q00DD00025Q00202Q0002000200014Q000300016Q000200036Q00029Q0000017Q00013Q0003093Q00536574412Q63656E7402064Q00EE00025Q00202Q0002000200014Q000300016Q0002000200016Q00028Q00017Q00013Q00030B3Q005365744475726174696F6E02064Q00EE00025Q00202Q0002000200014Q000300016Q0002000200016Q00028Q00017Q000F3Q0003083Q00556E6C6F616465642Q0103073Q0044657374726F7903043Q0053746F70030D3Q00436C656172526567697374727903043Q004D616964030A3Q00446F436C65616E696E6703073Q0057696E646F777303063Q0057696E646F770003053Q00436C65617203073Q00546F2Q676C657303073Q004F7074696F6E7303073Q004368616E676564030D3Q00446973636F2Q6E656374412Q6C012D3Q0020102Q013Q00010006930001000400013Q00049F012Q000400012Q0024012Q00013Q0030053Q000100022Q007000015Q0020102Q01000100032Q005E2Q01000100012Q0070000100013Q0020102Q01000100032Q005E2Q01000100012Q0070000100023Q0020102Q01000100032Q005E2Q01000100012Q0070000100033Q0020102Q01000100032Q006F0001000100014Q000100043Q00202Q0001000100044Q0001000100014Q000100053Q00202Q0001000100054Q00010001000100202Q00013Q000600202Q0001000100074Q0001000200012Q002A2Q015Q0010563Q000800010030053Q0009000A2Q0070000100063Q0020102Q010001000B2Q005E2Q01000100012Q0070000100073Q0012910002000C4Q001E000300034Q004D2Q01000300012Q0070000100073Q0012910002000D4Q001E000300034Q004D2Q01000300012Q0070000100083Q0020102Q010001000E00201100010001000F2Q00042Q01000200012Q0024012Q00017Q00", GetFEnv(), ...);
