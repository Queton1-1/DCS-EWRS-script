--WhiskeyTangoFoxtrot_3 EWRS Script v15.9 - Stable
--[[ Changelog
    15.9h by Quéton
    - Ajout appareils
    - Ajout d'options au menu
    - Modifications mineures et refactor de quelques fonctions

    15.9b by Quéton
    - Suppr. dépendance MIST
    - Ajout table pour ajout radar dans réseau
    - Modification du modèle de detection, range => détection DCS des radars
    - Ajout appareils

    15.9 
    - Stable by WhiskeyTangoFoxtgrot_3
--]]

-- === CONFIGURATION ===
local EWRS_SUBSTRING = {
    "EWR",
    "AWACS",
    "SAM",
    "SA",
}                                   -- Pattern in EWR/SAM/AWACS 's name to find to add in radar network
local ALLOWED_RED = true    -- Witch side to receive reports
local ALLOWED_BLUE = true   -- Witch side to receive reports
local ALLOWED_TYPE={
    ["AJS37"]=true,
    ["C-101EB"]=true,
    ["C-101CC"]=true,
    ["C-130J-30"]=false,
    ["F-4E-45MC"]=true,
    ["F-5E-3"]=true,
    ["F-5E"]=true,
    ["F-14A-135-GR"]=true,
    ["F-14B"]=true,
    ["J-11A"]=true,
    ["L-39C"]=true,
    ["L-39ZA"]=true,
    ["MB-339A"]=true,
    ["MB-339APAN"]=true,
    ["Mirage-F1B"]=true,
    ["Mirage-F1BD"]=true,
    ["Mirage-F1BE"]=true,
    ["Mirage-F1BQ"]=true,
    ["Mirage-F1DDA"]=true,
    ["MiG-15bis"]=true,
    ["MiG-19P"]=true,
    ["MiG-21Bis"]=true,
    ["MiG-29A"]=true,
    ["MiG-29S"]=true,
    ["MiG-29G"]=true,
    ["MiG-29 Fulcrum"]=true,
    ["Su-25"]=false,
    ["Su-25T"]=false,
    ["Su-27"]=true,
    ["Su-33"]=true,
    ["Yak-52"]=false,
}
local allowedAllType = false
local NORMAL_SCAN_INTERVAL = 25		-- Frequency of EWR callout information when enemy airgcraft is determined to be outside of close threshhold range. Default is 25 seconds.
local CLOSE_SCAN_INTERVAL = 3			-- Frequency of EWR callout information when enemy aircraft is determined to be withing close threshold range (within 5nm of Player).
local NORMAL_MESSAGE_DURATION = 15	-- Length of time that EWR callout information is presented on screen for the Player.
local CLOSE_MESSAGE_DURATION = 2		-- Length of time that EWR callout information in presented on screen when enemy is within 5nm. 
local RADAR_RANGE_NM = 150			-- Range threshold of radar for radar units. default 80nm
local CLOSE_RANGE_THRESHOLD = 10	-- Range threshold for close ewr callouts.
local CLOSE_CUE_THRESHOLD = 5  		-- Range threshold after which clock direction & relative altitude are provided in EWR callouts.
local ALT_FLOOR_FEET = 50		-- Altitude floor under which enemy aircraft are hidden from EWR callouts.
local maxContacts = 2				-- Limit on # of aircraft to be displayed on EWR callouts.
local METERS_PER_NM = 1852			-- Constant used to convert distance to nautical miles.
local ewrsEnabled = false			-- Initial setting of EWR callouts, hidden until player turns them on in radio options.
local playerUnit = nil				-- Initial setting for player value for mission start.
local playersGroupIdList={}         -- Initial setting for multiplayer value for mission start.
local EventsHandler={}              -- EventHandler list
local playersReport={}              -- Report option save

-- === LOCALS VARS ===
-- LUA ORIGINAL
local MathRan = math.random
local StrMatch = string.match
local StrSub = string.sub
local Floor = math.floor
-- LUA DCS API
local Scheduler=timer.scheduleFunction
local Now=timer.getTime
local GetZone=trigger.misc.getZone
local OutText=trigger.action.outText
local OutTextForCoalition=trigger.action.outTextForCoalition
local OutTextForGroup=trigger.action.outTextForGroup
local Log=env.info

-- === UTILITY FUNCTIONS ===
local function Get2DDistance(unit1, unit2)
    local p1 = unit1:getPosition().p
    local p2 = unit2:getPosition().p
    return math.sqrt((p1.x - p2.x)^2 + (p1.z - p2.z)^2)
end

local function GetAltitudeFeet(unit)
    return unit:getPoint().y * 3.28084
end

local function GetAGLFeet(unit)
    local pos = unit:getPoint()
    local terrain = land.getHeight({x = pos.x, y = pos.z})
    return (pos.y - terrain) * 3.28084
end

local function GetBearingToEnemy(player, enemy)
    local pPos = player:getPoint()
    local ePos = enemy:getPoint()
    local angleRad = math.atan2(ePos.z - pPos.z, ePos.x - pPos.x)
    local angleDeg = math.deg(angleRad)
    if angleDeg < 0 then angleDeg = angleDeg + 360 end
    return angleDeg
end

local function GetAspect(player, enemy)
    local dx = player:getPoint().x - enemy:getPoint().x
    local dz = player:getPoint().z - enemy:getPoint().z
    local angleToPlayer = math.deg(math.atan2(dz, dx))
    if angleToPlayer < 0 then angleToPlayer = angleToPlayer + 360 end

    local headingRad = enemy:getPosition().heading
    if not headingRad then
        local v = enemy:getVelocity()
        if v then headingRad = math.atan2(v.z, v.x) end
    end
    if not headingRad then return "Unknown" end

    local enemyHeading = math.deg(headingRad)
    if enemyHeading < 0 then enemyHeading = enemyHeading + 360 end

    local delta = (enemyHeading - angleToPlayer + 360) % 360
    if delta <= 45 or delta >= 315 then return "Hot"
    elseif delta >= 135 and delta <= 225 then return "Cold"
    elseif delta > 45 and delta < 135 then return "Flanking Left"
    else return "Flanking Right" end
end

local function GetRelativeClock(player, enemy)
    local headingRad = player:getPosition().heading
    if not headingRad then
        local vel = player:getVelocity()
        if vel and (vel.x ~= 0 or vel.z ~= 0) then
            headingRad = math.atan2(vel.z, vel.x)
        end
    end
    if not headingRad then return "unknown o'clock" end

    local headingDeg = math.deg(headingRad)
    if headingDeg < 0 then headingDeg = headingDeg + 360 end
    local bearing = GetBearingToEnemy(player, enemy)
    local rel = (bearing - headingDeg + 360) % 360
    local clock = Floor((rel + 15) / 30) % 12
    return (clock == 0 and 12 or clock) .. " o'clock"
end

local function GetRelativeAltitude(player, enemy)
    local diff = GetAltitudeFeet(enemy) - GetAltitudeFeet(player)
    if math.abs(diff) < 500 then return "level"
    elseif diff > 0 then return "high"
    else return "low" end
end

-- === FORMATTING ===
local function FormatAltitudeText(alt)
    if alt < 1000 then
        return "Cherubs " .. Floor(alt / 100 + 0.5)
    else
        return "Angels " .. Floor(alt / 1000 + 0.5)
    end
end

local function FormatContactLine(typeName, bearing, distanceNM, altitudeFeet, aspect, clockCue, altCue)
    local cueString = ""
    if clockCue and altCue then
        cueString = string.format(" (%s, %s)", clockCue, altCue)
    end
    return string.format("%-16s BRAA %03.0f° / %2.0fnm  %-13s  %-14s%s",
        typeName,
        bearing,
        distanceNM,
        FormatAltitudeText(altitudeFeet),
        aspect,
        cueString
    )
end

-- === PLAYER & RADAR DETECTION ===
local function GetActiveAirUnits(side)
    local units = {}
    for _, group in ipairs(coalition.getGroups(side, Group.Category.AIRPLANE)) do
        for _, unit in ipairs(group:getUnits()) do
            if unit and unit:isActive() then table.insert(units, unit) end
        end
    end
    return units
end

local function GetAllRadarUnits(side)
    local radars = {}
    local function add(category)
        for _, group in ipairs(coalition.getGroups(side, category)) do
            for i=1, #EWRS_SUBSTRING do
                if group:getName():match(EWRS_SUBSTRING[i]) then
					for _, unit in ipairs(group:getUnits()) do
						if unit and unit:isActive() then table.insert(radars, unit) end
					end
                end
            end
        end
    end
    add(Group.Category.AIRPLANE)
    add(Group.Category.GROUND)
    return radars
end

-- === MAIN EWRS SCAN ===
local function PerformEWRScan(playerUnit)
    if playerUnit:isExist()==false then return end
    if playersReport and playersReport[playerUnit:getGroup():getID()]==false then return Now() + NORMAL_SCAN_INTERVAL end

    local found, side
    if playerUnit then
        found = playerUnit
        side = playerUnit:getCoalition()
    else
        return Now() + NORMAL_SCAN_INTERVAL
    end
    if not found then return Now() + 5 end
    playerUnit = found
    local enemySide = (side == coalition.side.BLUE) and coalition.side.RED or coalition.side.BLUE
    local radars = GetAllRadarUnits(side)
    local enemies = GetActiveAirUnits(enemySide)
    local seen = {}
    local contacts = {}
    local threatClose = false
    for _, radar in ipairs(radars) do
        for _, enemy in ipairs(enemies) do
            local name = enemy:getName()
            local agl = GetAGLFeet(enemy)
            local isDetected=radar:getController():isTargetDetected(enemy,1,4)
            if isDetected and enemy:getLife() > 1 then
                local distMeters = Get2DDistance(radar, enemy)
                if distMeters <= RADAR_RANGE_NM * METERS_PER_NM then
                    seen[name] = true
                    local distPlayer = Get2DDistance(playerUnit, enemy)
                    local distNM = distPlayer / METERS_PER_NM
                    if distNM <= CLOSE_RANGE_THRESHOLD then threatClose = true end

                    local bearing = GetBearingToEnemy(playerUnit, enemy)
                    local alt = GetAltitudeFeet(enemy)
                    local aspect = GetAspect(playerUnit, enemy)
                    local clockCue, altCue = nil, nil
                    if distNM <= CLOSE_CUE_THRESHOLD then
                        clockCue = GetRelativeClock(playerUnit, enemy)
                        altCue = GetRelativeAltitude(playerUnit, enemy)
                    end

                    table.insert(contacts, {
                        sortDistance = distPlayer,
                        line = FormatContactLine(enemy:getTypeName(), bearing, distNM, alt, aspect, clockCue, altCue)
                    })
                end
            end
        end
    end

    local duration = threatClose and CLOSE_MESSAGE_DURATION or NORMAL_MESSAGE_DURATION
    local interval = threatClose and CLOSE_SCAN_INTERVAL or NORMAL_SCAN_INTERVAL
    local report = "EWRS | Bogey Dope for "..playerUnit:getPlayerName().." :\n"
    local reportClear = "EWRS | Bogey Dope for "..playerUnit:getPlayerName().." : Clear."
    if #contacts == 0 then OutTextForGroup(playerUnit:getGroup():getID(), reportClear, duration) return Now() + NORMAL_SCAN_INTERVAL end
    table.sort(contacts, function(a, b) return a.sortDistance < b.sortDistance end)
    for i = 1, math.min(#contacts, maxContacts) do
        report = report .. "  ".. contacts[i].line .. "\n"
    end
    OutTextForGroup(playerUnit:getGroup():getID(), report, duration)
    return Now() + interval
end

-- === RADIO COMMANDS ===
local function ReportFriendlyPicture(playerUnit)
    if playerUnit:isExist()==false then return end
    local found, side
    if playerUnit then
        found = playerUnit
        side = playerUnit:getCoalition()
    else
        return Now() + NORMAL_SCAN_INTERVAL
    end
    local radars = GetAllRadarUnits(side)
    local units = GetActiveAirUnits(side)
    local seen, contacts = {}, {}

    for _, radar in ipairs(radars) do
        for _, unit in ipairs(units) do
            local isDetected=radar:getController():isTargetDetected(unit,1,4)
            if unit:getLife() > 1 and unit ~= playerUnit and isDetected then
                local dist = Get2DDistance(radar, unit)
                if dist <= RADAR_RANGE_NM * METERS_PER_NM then
                    seen[unit:getName()] = true
                    local distPlayer = Get2DDistance(playerUnit, unit)
                    local bearing = GetBearingToEnemy(playerUnit, unit)
                    local alt = GetAltitudeFeet(unit)
                    local aspect = GetAspect(playerUnit, unit)
                    table.insert(contacts, {
                        sortDistance = distPlayer,
                        line = FormatContactLine(unit:getTypeName(), bearing, distPlayer / METERS_PER_NM, alt, aspect)
                    })
                end
            end
        end
    end

    if #contacts == 0 then
        OutTextForGroup(playerUnit:getGroup():getID(), "EWRS | No Buddy detected.", 5)
        return
    end

    table.sort(contacts, function(a, b) return a.sortDistance < b.sortDistance end)
    local report = "EWRS | 'Buddy' situation for "..playerUnit:getPlayerName().." :\n\n"
    for i = 1, math.min(#contacts, maxContacts) do
        report = report .. contacts[i].line .. "\n"
    end
    OutTextForGroup(playerUnit:getGroup():getID(), report, NORMAL_MESSAGE_DURATION)
end

local function ReportEnemyHelos(playerUnit)
    if playerUnit:isExist()==false then return end
    local found, side
    if playerUnit then
        found = playerUnit
        side = playerUnit:getCoalition()
    else
        return Now() + NORMAL_SCAN_INTERVAL
    end
    local enemySide = (side == coalition.side.BLUE) and coalition.side.RED or coalition.side.BLUE
    local radars = GetAllRadarUnits(side)
    local helos = coalition.getGroups(enemySide, Group.Category.HELICOPTER)
    local seen, contacts = {}, {}

    for _, radar in ipairs(radars) do
        for _, group in ipairs(helos) do
            for _, unit in ipairs(group:getUnits()) do
                local name = unit:getName()
                local isDetected=radar:getController():isTargetDetected(unit,1,4)
                if unit and unit:isActive() and unit:getLife() > 1 and isDetected then
                    seen[name] = true
                    local dist = Get2DDistance(playerUnit, unit)
                    local bearing = GetBearingToEnemy(playerUnit, unit)
                    local alt = GetAltitudeFeet(unit)
                    local aspect = GetAspect(playerUnit, unit)
                    table.insert(contacts, {
                        sortDistance = dist,
                        line = FormatContactLine(unit:getTypeName(), bearing, dist / METERS_PER_NM, alt, aspect)
                    })
                end
            end
        end
    end

    if #contacts == 0 then
        OutTextForGroup(playerUnit:getGroup():getID(), "EWRS | No Bandits detected.", 5)
        return
    end

    table.sort(contacts, function(a, b) return a.sortDistance < b.sortDistance end)
    local report = "EWRS | Bandits choppers situation for "..playerUnit:getPlayerName().." :\n\n"
    for i = 1, math.min(#contacts, maxContacts) do
        report = report .. contacts[i].line .. "\n"
    end
    OutTextForGroup(playerUnit:getGroup():getID(), report, NORMAL_MESSAGE_DURATION)
end

-- === RADIO MENU INIT ===
local function AddRadioMenuMultiplayer(playerUnit)
    local groupID = playerUnit:getGroup():getID()
    local _match=0
    if ALLOWED_RED==false and playerUnit:getCoalition()==1 then OutTextForGroup (playerUnit:getGroup():getID(), "WhiskeyTango EWRS | unavailable for Red coalition.", NORMAL_MESSAGE_DURATION) return end
    if ALLOWED_BLUE==false and playerUnit:getCoalition()==2 then OutTextForGroup (playerUnit:getGroup():getID(), "WhiskeyTango EWRS | unavailable for Blue coalition.", NORMAL_MESSAGE_DURATION) return end
    for i=1, #playersGroupIdList do
        if playerUnit:getGroup():getID() == playersGroupIdList[i] then _match=_match+1 end
    end
    playersReport[groupID] = false
    if ALLOWED_TYPE[playerUnit:getTypeName()]==true or allowedAllType==true then
        if _match==0 then
            playersGroupIdList[#playersGroupIdList+1]=groupID
            local SubMenu = missionCommands.addSubMenuForGroup(groupID,'WhiskeyTango EWRS')
            missionCommands.addCommandForGroup(groupID, "Toggle EWRS Callouts", SubMenu, function()
                playersReport[groupID] = not playersReport[groupID]
                OutTextForGroup(groupID, "EWRS | Callouts are now " .. (playersReport[groupID] and "enabled" or "disabled") .. " for this group.", 5)
            end)
            missionCommands.addCommandForGroup(groupID, "Report more contacts", SubMenu, function()
                maxContacts=maxContacts+1
                OutTextForGroup(groupID, "EWRS | Will report "..maxContacts.." contacts", 5)
            end)
            missionCommands.addCommandForGroup(groupID, "Report less contacts", SubMenu, function()
                if maxContacts>=2 then maxContacts=maxContacts-1 else maxContacts=1 end
                OutTextForGroup(groupID, "EWRS | Will report "..maxContacts.." contacts", 5)
            end)
            missionCommands.addCommandForGroup(groupID, "Request Friendly Picture", SubMenu, ReportFriendlyPicture, playerUnit)
            missionCommands.addCommandForGroup(groupID, "Request Enemy Helicopter Picture", SubMenu, ReportEnemyHelos, playerUnit)
            OutTextForGroup(groupID, "EWRS | Callouts available for this group.", 5)
            Scheduler(function() return PerformEWRScan(playerUnit) end, {}, Now() + 1)
        else
            OutTextForGroup(groupID, "EWRS | Callouts available for this group.", 5)
            Scheduler(function() return PerformEWRScan(playerUnit) end, {}, Now() + 1)
        end
    elseif ALLOWED_TYPE[playerUnit:getTypeName()]==false then
        Log("WhiskeyTango EWRS | Unauthorized type : "..playerUnit:getTypeName(),30)
    else
        Log("WhiskeyTango EWRS | No datas for this type : "..playerUnit:getTypeName(),30)
    end
end

function EventsHandler:onEvent(event)
    if event.id == world.event.S_EVENT_BIRTH and event.initiator then
        local birthCategory=event.initiator:getDesc()["category"]
        if birthCategory==0 and event.initiator:getPlayerName() then AddRadioMenuMultiplayer(event.initiator) end
    elseif world.event.S_EVENT_MARK_CHANGE == event.id and event.coalition ~= 0 then
    elseif world.event.S_EVENT_MARK_REMOVED == event.id and event.coalition ~= 0 then
        if (StrMatch(event.text,"wtewrs4")) then maxContacts=4
        elseif (StrMatch(event.text,"wtewrs2")) then maxContacts=2
        elseif (StrMatch(event.text,"wtewrs1")) then maxContacts=1
        elseif (StrMatch(event.text,"wtewrsallow")) then allowedAllType=true
        elseif (StrMatch(event.text,"wtewrsrestrict")) then allowedAllType=false
        end
    end
end
-- === INITIALIZATION ===
OutText("WhiskeyTango EWRS | Credits : WhiskeyTangoFoxtrot_3 & Quéton", 5)
Log("WhiskeyTango EWRS | Credits : WhiskeyTangoFoxtrot_3 & Quéton")
world.addEventHandler(EventsHandler)
