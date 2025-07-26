/* AsteroidsGame
 * Author: Dimuthu Jayathunga (20210249/w1870624)
 * Creation date: 2025-06-19
 */

MACHINE
    AsteroidsGame

// Define sets of constants used in the game    
SETS
    REPORT = {SUCCESSFULLY_MOVED, CANNOT_MOVE_OUT_OF_KNOWN_SPACE, INSUFFICIENT_POWER, SUCCESSFULLY_TURNED, CANNOT_MOVE_IN_THAT_DIRECTION, SUCCESSFULLY_FIRED, NO_ASTEROID_HIT, INSUFFICIENT_POWER_TO_FIRE, CANNOT_MOVE_UP,CANNOT_MOVE_DOWN, CANNOT_MOVE_FORWARD, CANNOT_MOVE_BACKWARD,FAIL_MOVED};
    MOVEMENT = {MOVE_UP, MOVE_DOWN, MOVE_FORWARD, MOVE_BACKWARD, TURN_CLOCKWISE, TURN_COUNTERCLOCKWISE, FIRE_LASER, DONNOT_FIRE_LASER_IT_IS_A_LARGE_ASTEROID, FIRE_LASER_IT_IS_A_SMALL_ASTEROID};
    DOCKED_STATUS = {YES, NO};
    GAME_STATUS = {GAME_WON, GAME_LOST, ONGOING};
    DIRECTION = {DIR_UP, DIR_DOWN, DIR_LEFT, DIR_RIGHT}

// Define game constraints and configuration constants
CONSTANTS
    normalMovePower, initialPower, laserPower,
      spaceX, spaceY, space, initialLargeAsteroids, initialSmallAsteroids, homeBase, starBase, turnPower
    
PROPERTIES
    spaceX = 1..12 &     // Define the game space as a 12x10 grid
    spaceY = 1..10 &
    space = spaceX * spaceY &
    initialLargeAsteroids <: space &
    initialLargeAsteroids = {2|->1, 3|->7, 5|->4, 6|->2, 6|->3, 6|->7, 6|->8, 7|->6, 8|->1, 8|->5, 8|->9, 10|->7, 10|->9, 11|->8} &  // Define initial large asteroid positions
    initialSmallAsteroids <: space &
    initialSmallAsteroids = {1|->6, 2|->4, 2|->7, 3|->4, 4|->6, 4|->7, 4|->9, 5|->6, 6|->5, 7|->5, 8|->4, 9|->6, 10|->2, 10|->5, 11|->5, 12|->4, 12|->9} &  // Define initial small asteroid positions
    initialLargeAsteroids /\ initialSmallAsteroids = {} &
    homeBase : space & homeBase = 1|->1 & //Define key locations
    starBase : space & starBase = 8|->7 &
    homeBase /: (initialLargeAsteroids \/ initialSmallAsteroids) &  // Ensure bases are not blocked by asteroids
    starBase /: (initialLargeAsteroids \/ initialSmallAsteroids) &
    normalMovePower = 5 &  // Define power 
    initialPower = 200 &
    turnPower = 3 &
    laserPower = 20
  
// Helper function  
DEFINITIONS
    isWithinSpace(xx, yy) == (xx |-> yy : space);                                        // Check if coordinates are within game boundaries
    isHitLargeAsteroid(xx, yy) == (xx |-> yy : largeAsteroids);                          // Check if position contains a large asteroid
    isHitSmallAsteroid(xx, yy) == (xx |-> yy : smallAsteroids);                          // Check if position contains a small asteroid
    isHitAsteroid(xx, yy) == (isHitLargeAsteroid(xx, yy) or isHitSmallAsteroid(xx, yy)); // Check if position contains any asteroid
    isDocked == (xPosition |-> yPosition = starBase);                                    // Check if spaceship is docked at star base
    isGameFinished == isDocked or (power < normalMovePower);                             // Check if game is finished
    getAdjacentSquares(xx, yy) == {pos | pos : space &                                   // Get all adjacent squares with center
        (pos = (xx |-> yy) or 
         pos = ((xx-1) |-> yy) or 
         pos = ((xx+1) |-> yy) or 
         pos = (xx |-> (yy-1)) or 
         pos = (xx |-> (yy+1)))};                                  
    getTargetSquare(xx, yy, dir) ==                                                      // Calculate target square based on current position and direction
        IF dir = DIR_UP THEN (xx |-> (yy + 1))
        ELSIF dir = DIR_DOWN THEN (xx |-> (yy - 1))
        ELSIF dir = DIR_LEFT THEN ((xx - 1) |-> yy)
        ELSE ((xx + 1) |-> yy) END;               
                                
    // Visual representation
    ANIMATION_FUNCTION == ({rr,cc,ii | rr:spaceY & cc:spaceX &            
            (IF (cc = 8 & rr = 11-7 ) // Star base position 
                THEN
                    ii = 3
                ELSE
                    IF (cc |-> (11 - rr) : largeAsteroids)  // Large asteroid
                    THEN
                        ii = 1
                    ELSE
                        IF (cc |-> (11 - rr) : smallAsteroids)  // Small asteroid
                        THEN
                            ii = 7
                        ELSE
                            IF (cc = xPosition & rr = (11 - yPosition))  // Spaceship position
                            THEN
                                // Choose spaceship image based on direction
                                ii = 
                                    IF direction = DIR_UP THEN 2
                                    ELSIF direction = DIR_DOWN THEN 4
                                    ELSIF direction = DIR_LEFT THEN 5
                                    ELSE 6 END
                            ELSE
                                ii = 0  // Empty space
                            END
                        END
                    END
                END)});
    ANIMATION_IMG0 == "ani/empty.gif";
    ANIMATION_IMG1 == "ani/asteroid.gif";
    ANIMATION_IMG2 == "ani/spaceship_up.gif";
    ANIMATION_IMG3 == "ani/starbase.gif";
    ANIMATION_IMG4 == "ani/spaceship_down.gif";
    ANIMATION_IMG5 == "ani/spaceship_left.gif";
    ANIMATION_IMG6 == "ani/spaceship_right.gif";
    ANIMATION_IMG7 == "ani/small_asteroid.gif";

// Declare variables    
VARIABLES
    xPosition, yPosition, power, takenRoute, movements, direction, largeAsteroids, smallAsteroids
    
INVARIANT
    xPosition : spaceX &                     // Spaceship position must be within game boundaries
    yPosition : spaceY &                     
    xPosition |-> yPosition /: (largeAsteroids \/ smallAsteroids) &   // Spaceship position and asteroid cannot same square
    power : NAT &
    takenRoute : seq(space) &                // Route and movements are sequences
    movements : seq(MOVEMENT) & 
    direction : DIRECTION &                 // Direction must be one of the four cardinal directions
    largeAsteroids <: space &               // Asteroids must be within game space
    smallAsteroids <: space &
    largeAsteroids /\ smallAsteroids = {}   // Large and small asteroids cannot same position
    
// Initialize game state
INITIALISATION
    power := initialPower ||                          // Place initial power 
    xPosition := prj1(spaceX, spaceY)(homeBase) ||    // Extract X coordinate from homeBase
    yPosition := prj2(spaceX, spaceY)(homeBase) ||    // Extract Y coordinate from homeBase
    takenRoute := [homeBase] ||                       // Start route with home base
    movements := [] ||                                // Initialize movements with empty sequences
    direction := DIR_RIGHT ||                         // Start facing right
    largeAsteroids := initialLargeAsteroids ||        // Place initial large asteroids
    smallAsteroids := initialSmallAsteroids           // Place initial small asteroids
    
OPERATIONS
    // Moves Up
    report, movement <-- MoveUp =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        IF
            direction = DIR_UP
        THEN
            IF
		  (power >= normalMovePower)
            THEN
                IF
                    isWithinSpace(xPosition, yPosition + 1)
                THEN
                    //Check UP Square is not a larger or small Asteroid for Move the spaceship
                    IF 
                        not(isHitAsteroid(xPosition, yPosition + 1))
                    THEN
                  		    //Check if the power is enough to move
                        IF
                            (power - normalMovePower >= 0)    // Check the power will go negative
                        THEN
                            yPosition := yPosition + 1 ||
                            power := power - normalMovePower ||
                            takenRoute := takenRoute <- (xPosition |-> yPosition + 1) ||
                            movements := movements <- MOVE_UP ||
                            report := SUCCESSFULLY_MOVED ||
                            movement := MOVE_UP
                        ELSE
                            yPosition := yPosition + 1 ||
                            power := 0 ||
                            takenRoute := takenRoute <- (xPosition |-> yPosition + 1) ||
                            movements := movements <- MOVE_UP ||
                            report := FAIL_MOVED ||
                            movement := MOVE_UP
                        END
                    ELSE
			//check is it lager/small Asteroid for Fire
                        IF
                            ((xPosition |-> yPosition + 1): largeAsteroids)
                        THEN
			    report := CANNOT_MOVE_UP ||
                            movement := DONNOT_FIRE_LASER_IT_IS_A_LARGE_ASTEROID
                        ELSE
                            report := CANNOT_MOVE_UP ||
                            movement := FIRE_LASER_IT_IS_A_SMALL_ASTEROID
                        END
                    END
                ELSE
                    report := CANNOT_MOVE_OUT_OF_KNOWN_SPACE ||
                    movement := MOVE_UP
                END
            ELSE
                report := INSUFFICIENT_POWER ||
                movement := MOVE_UP
            END
        ELSE
            report := CANNOT_MOVE_IN_THAT_DIRECTION ||
            movement := MOVE_UP
        END
    END;
    
    // Moves Down 
    report, movement <-- MoveDown =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        IF
            direction = DIR_DOWN
        THEN
            IF
		  (power >= normalMovePower)
            THEN
                IF
                    isWithinSpace(xPosition, yPosition - 1)
                THEN
                    //Check Down Square is not a larger or small Asteroid for Move the spaceship
                    IF 
                        not(isHitAsteroid(xPosition, yPosition - 1))
                    THEN
                  		    //Check if the power is enough to move
                        IF
                            (power - normalMovePower >= 0)
                        THEN
                            yPosition := yPosition - 1 ||
                            power := power - normalMovePower ||
                            takenRoute := takenRoute <- (xPosition |-> yPosition - 1) ||
                            movements := movements <- MOVE_DOWN ||
                            report := SUCCESSFULLY_MOVED ||
                            movement := MOVE_DOWN
                        ELSE
                            yPosition := yPosition - 1 ||  
                            power := 0 ||
                            takenRoute := takenRoute <- (xPosition |-> yPosition - 1) ||
                            movements := movements <- MOVE_DOWN ||
                            report := FAIL_MOVED ||
                            movement := MOVE_DOWN
                        END
                    ELSE
			//check is it lager/small Asteroid for Fire
                        IF
                            ((xPosition |-> yPosition - 1) : largeAsteroids)
                        THEN
                            report := CANNOT_MOVE_DOWN ||
                            movement := DONNOT_FIRE_LASER_IT_IS_A_LARGE_ASTEROID
                        ELSE
                            report := CANNOT_MOVE_DOWN ||
                            movement := FIRE_LASER_IT_IS_A_SMALL_ASTEROID
                        END
                    END
                ELSE
                    report := CANNOT_MOVE_OUT_OF_KNOWN_SPACE ||
                    movement := MOVE_DOWN
                END
            ELSE
                report := INSUFFICIENT_POWER ||
                movement := MOVE_DOWN
            END
        ELSE
            report := CANNOT_MOVE_IN_THAT_DIRECTION ||
            movement := MOVE_DOWN
        END
    END;
    
    // Moves Forward (Right) 
    report, movement <-- MoveForward =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        IF
            direction = DIR_RIGHT
        THEN
            IF
		  (power >= normalMovePower)
            THEN
                IF
                    isWithinSpace(xPosition + 1, yPosition)
                THEN
                    //Check Right Square is not a larger or small Asteroid for Move the spaceship
                    IF 
                        not(isHitAsteroid(xPosition + 1, yPosition))
                    THEN
                  		    //Check if the power is enough to move Right
                        IF
                            (power - normalMovePower >= 0)
                        THEN
                            xPosition := xPosition + 1 ||
                            power := power - normalMovePower ||
                            takenRoute := takenRoute <- (xPosition + 1 |-> yPosition) ||
                            movements := movements <- MOVE_FORWARD ||
                            report := SUCCESSFULLY_MOVED ||
                            movement := MOVE_FORWARD
                        ELSE
                            xPosition := xPosition + 1 ||
                            power := 0 ||
                            takenRoute := takenRoute <- (xPosition + 1 |-> yPosition) ||
                            movements := movements <- MOVE_FORWARD ||
                            report := FAIL_MOVED ||
                            movement := MOVE_FORWARD
                        END
                    ELSE
			//check is it lager/small Asteroid for Fire
                        IF
			      ((xPosition + 1 |-> yPosition): largeAsteroids)
                        THEN
                            report := CANNOT_MOVE_FORWARD ||
                            movement := DONNOT_FIRE_LASER_IT_IS_A_LARGE_ASTEROID
                        ELSE
			    report := CANNOT_MOVE_FORWARD ||
                            movement := FIRE_LASER_IT_IS_A_SMALL_ASTEROID
                        END
                    END
                ELSE
                    report := CANNOT_MOVE_OUT_OF_KNOWN_SPACE ||
                    movement := MOVE_FORWARD
                END
            ELSE
                report := INSUFFICIENT_POWER ||
                movement := MOVE_FORWARD
            END
        ELSE
            report := CANNOT_MOVE_IN_THAT_DIRECTION ||
            movement := MOVE_FORWARD
        END
    END;
    
    // Moves Backward (Left) 
    report, movement <-- MoveBackward =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        IF
            direction = DIR_LEFT
        THEN
            IF
		  (power >= normalMovePower)
            THEN
                IF
                    isWithinSpace(xPosition - 1, yPosition)
                THEN
                    //Check Left Square is not a larger or small Asteroid for Move the spaceship
                    IF 
                        not(isHitAsteroid(xPosition - 1, yPosition))
                    THEN
                  		    //Check if the power is enough to move Left
                        IF
                            (power - normalMovePower >= 0)
                        THEN
                            xPosition := xPosition - 1 ||
                            power := power - normalMovePower ||
                            takenRoute := takenRoute <- (xPosition - 1 |-> yPosition) ||
                            movements := movements <- MOVE_BACKWARD ||
                            report := SUCCESSFULLY_MOVED ||
                            movement := MOVE_BACKWARD
                        ELSE
                            xPosition := xPosition - 1 ||
                            power := 0 ||
                            takenRoute := takenRoute <- (xPosition - 1 |-> yPosition) ||
                            movements := movements <- MOVE_BACKWARD ||
                            report := FAIL_MOVED ||
                            movement := MOVE_BACKWARD
                        END
                    ELSE
			//check is it lager/small Asteroid for Fire
                        IF
                            ((xPosition - 1 |-> yPosition) : largeAsteroids)
                        THEN
			    report := CANNOT_MOVE_BACKWARD ||
                            movement := DONNOT_FIRE_LASER_IT_IS_A_LARGE_ASTEROID
                        ELSE
                            report := CANNOT_MOVE_BACKWARD ||
                            movement := FIRE_LASER_IT_IS_A_SMALL_ASTEROID
                        END
                    END
                ELSE
                    report := CANNOT_MOVE_OUT_OF_KNOWN_SPACE ||
                    movement := MOVE_BACKWARD
                END
            ELSE
                report := INSUFFICIENT_POWER ||
                movement := MOVE_BACKWARD
            END
        ELSE
            report := CANNOT_MOVE_IN_THAT_DIRECTION ||
            movement := MOVE_BACKWARD
        END
    END;
    
    // Turns Clockwise
    report, movement <-- TurnClockwise =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        BEGIN
            IF
		  (power >= turnPower)
            THEN
                direction := 
                    IF direction = DIR_UP THEN DIR_RIGHT
                    ELSIF direction = DIR_RIGHT THEN DIR_DOWN
                    ELSIF direction = DIR_DOWN THEN DIR_LEFT
                    ELSE DIR_UP END ||
                power := power - turnPower ||
                movements := movements <- TURN_CLOCKWISE ||
                report := SUCCESSFULLY_TURNED ||
                movement := TURN_CLOCKWISE
            ELSE
                report := INSUFFICIENT_POWER ||
                movement := TURN_CLOCKWISE
            END
        END
    END;
    
    // Turns Counterclockwise 
    report, movement <-- TurnCounterclockwise =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        BEGIN
            IF
		  (power >= turnPower)
            THEN
                direction := 
                    IF direction = DIR_UP THEN DIR_LEFT
                    ELSIF direction = DIR_LEFT THEN DIR_DOWN
                    ELSIF direction = DIR_DOWN THEN DIR_RIGHT
                    ELSE DIR_UP END ||
                power := power - turnPower ||
                movements := movements <- TURN_COUNTERCLOCKWISE ||
                report := SUCCESSFULLY_TURNED ||
                movement := TURN_COUNTERCLOCKWISE
            ELSE
                report := INSUFFICIENT_POWER ||
                movement := TURN_COUNTERCLOCKWISE
            END
        END
    END;
    
    // Fires Laser 
    report, movement <-- FireLaser =
    PRE
        report : REPORT & movement : MOVEMENT & not(isGameFinished)
    THEN
        IF
	      (power >= laserPower)
        THEN
	    // Calculates which square the laser will hit
            LET targetSquare BE targetSquare = getTargetSquare(xPosition, yPosition, direction) IN
		// Checks if the target square is within the space boundaries
                IF
                    isWithinSpace(prj1(spaceX, spaceY)(targetSquare), prj2(spaceX, spaceY)(targetSquare))
                THEN
		    // Check target square is Large Asteroid
                    IF
                        isHitLargeAsteroid(prj1(spaceX, spaceY)(targetSquare), prj2(spaceX, spaceY)(targetSquare))
                    THEN
                        LET newSmallAsteroids BE newSmallAsteroids = getAdjacentSquares(prj1(spaceX, spaceY)(targetSquare), prj2(spaceX, spaceY)(targetSquare)) /\ space IN
                            largeAsteroids := largeAsteroids - {targetSquare} ||
                            smallAsteroids := smallAsteroids \/ newSmallAsteroids ||
                            power := (IF xPosition |-> yPosition : newSmallAsteroids THEN 0 ELSE power - laserPower END) ||
                            movements := movements <- FIRE_LASER ||
                            report := SUCCESSFULLY_FIRED ||
                            movement := FIRE_LASER
                        END
                    ELSE
		        // Check target square is Small Asteroid
                        IF
                            isHitSmallAsteroid(prj1(spaceX, spaceY)(targetSquare), prj2(spaceX, spaceY)(targetSquare))
                        THEN
                            smallAsteroids := smallAsteroids - {targetSquare} ||
                            power := power - laserPower ||
                            movements := movements <- FIRE_LASER ||
                            report := SUCCESSFULLY_FIRED ||
                            movement := FIRE_LASER
                        ELSE
                            power := power - laserPower ||
                            movements := movements <- FIRE_LASER ||
                            report := NO_ASTEROID_HIT ||
                            movement := FIRE_LASER
                        END
                    END
                ELSE
                    power := power - laserPower ||
                    movements := movements <- FIRE_LASER ||
                    report := NO_ASTEROID_HIT ||
                    movement := FIRE_LASER
                END
            END
        ELSE
            report := INSUFFICIENT_POWER_TO_FIRE ||
            movement := FIRE_LASER
        END
    END;
    
    // Gives the current status of the space ship 
    currentLocation, currentPower, currentDirection <-- MissionStatus =
    BEGIN
        currentLocation := xPosition |-> yPosition ||
        currentPower := power ||
        currentDirection := direction
    END;
    
    // Gives the route that the space ship has travelled through 
    route <-- MissionRoute =
    BEGIN
        route := takenRoute
    END;
    
    // Reports whether the space ship is docked at the star base
    dockedStatus <-- DockedAtStarbase =
    PRE
        dockedStatus : DOCKED_STATUS
    THEN
        IF
            (isDocked)
        THEN
            dockedStatus := YES
        ELSE
            dockedStatus := NO
        END
    END;
    
    // Reports the game status
    status <-- GameStatus =
    PRE
        status : GAME_STATUS
    THEN
        IF
            (isDocked)
        THEN
            status := GAME_WON
        ELSE
            IF
                (power < normalMovePower)
            THEN
                status := GAME_LOST
            ELSE
                status := ONGOING
            END
        END
    END;
    
    // Gives all movements taken by the space ship 
    allMovements <-- takenMovements =
    BEGIN
        allMovements := movements
    END;
    
    // Resets the game, and starts again from the beginning 
    newGame =
    PRE
        isGameFinished
    THEN
        power := initialPower ||
        xPosition := prj1(spaceX, spaceY)(homeBase) ||
        yPosition := prj2(spaceX, spaceY)(homeBase) ||
        takenRoute := [homeBase] ||
        movements := [] ||
        direction := DIR_RIGHT ||
        largeAsteroids := initialLargeAsteroids ||
        smallAsteroids := initialSmallAsteroids
    END
END