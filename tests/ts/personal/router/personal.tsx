/*
 * @Date: 2021-03-03 11:01:17
 * @LastEditTime: 2021-05-07 11:38:39
 * @Description: 个人中心页路由
 * @FilePath: \vrn-pages\src\router\Personal.tsx
 */
import React from 'react';
import { Platform } from 'react-native';
import { createStackNavigator } from '@react-navigation/stack';
import { NavigationContainer, DefaultTheme } from '@react-navigation/native';
import { t } from '@hw-vmall/vrn-basic-comp';
import PersonalDeaultWeb from '../pages/personalpage';
import PersonalDeaultApk from '../pages/personalpage/index.native';
const PersonalRouters = ({ defaultRoute, ...personalProps }) => {
  const Stack = createStackNavigator();

  const MyTheme = {
    ...DefaultTheme,
    colors: {
      ...DefaultTheme.colors,
      background: 'transparent',
    },
  };

  return (
    <NavigationContainer theme={MyTheme}>
      <Stack.Navigator initialRouteName={defaultRoute}>
        <Stack.Screen
          name="PersonalDeault"
          options={{ headerShown: false, title: t('personal') }}
        >
          {(props) => {
            if (Platform.OS === 'web') {
              return <PersonalDeaultWeb {...personalProps} />;
            } else {
              return <PersonalDeaultApk {...personalProps} />;
            }
          }}
        </Stack.Screen>
      </Stack.Navigator>
    </NavigationContainer>
  );
};
export default PersonalRouters;
