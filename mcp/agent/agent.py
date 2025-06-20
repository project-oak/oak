#
# Copyright 2025 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

from google.adk.agents import Agent
import math


def get_user_location() -> dict:
    """Retrieves the current user's location.

    Returns:
        dict: status and a dictionary with coordinates (latitude and longitude) or error message.
    """
    return {
        "status": "success",
        "coordinates": {
            "latitude": 0.0,
            "longitude": 0.0,
        },
    }

def get_weather(latitude: float, longitude: float) -> dict:
    """Retrieves current weather for specified coordinates.

    Args:
        latitude (float): Latitude.
        longitude (float): Longitude.

    Returns:
        dict: status and weather or error msg.
    """
    if math.isclose(latitude, 0, rel_tol=1e-5) and math.isclose(longitude, 0, rel_tol=1e-5):
        return {
            "status": "success",
            "weather": (
                "The weather is sunny with a temperature of 30 degrees Celsius."
            ),
        }
    else:
        return {
            "status": "error",
            "error_message": f"Weather information for ('{latitude}','{longitude}') is not available.",
        }


root_agent = Agent(
    name="weather_agent",
    model="gemini-2.5-flash",
    description=(
        "Agent to answer questions about the weather at the current user's location."
    ),
    instruction=(
        "You are a helpful agent who can provide current user's location and also tell weather at this location."
    ),
    tools=[get_user_location, get_weather],
)
